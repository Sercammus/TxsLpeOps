{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Satisfiability
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module Satisfiability (
isTautology,
isSatisfiable,
isNotSatisfiable,
areSatisfiable,
areNotSatisfiable,
getSomeSolution,
getUniqueSolution,
restoreTdefs,
showSolution,
doVarSubst,
createVarSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.Identity as MonadId
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified EnvData
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified FreeVar
import qualified Solve
import qualified SolveDefs
import qualified SortId
import qualified SortOf
import qualified SMTData
import Constant hiding (sort)
import VarId
import ValExpr
import CstrId
import LPEPrettyPrint
import LPETypes
import ValExprVisitorM
import VarFactory
import ValFactory

-- Doing substitutions in expressions may result in (partially) undefined expressions!
-- (In particular, imagine substituting a constructor in an incompatible field access function.)
-- To handle this, each expression carries additional information, namely
-- a list of 'undefined variables', which are variables that represent undefined sub-expressions:
type UndefVExpr = (TxsDefs.VExpr, [VarId])

-- Manipulating expressions (e.g. substituting before SAT-solving) may require helper variables.
-- These variables are added to the TorXakis definitions in the environment of the monad.
-- To undo these additions, pass the original definitions to the following helper method:
restoreTdefs :: TxsDefs.TxsDefs -> IOC.IOC ()
restoreTdefs tdefs = do
    state <- MonadState.gets IOC.state
    let newState = state { IOC.tdefs = tdefs }
    MonadState.modify (\env -> env { IOC.state = newState })
-- restoreTdefs

-- Eliminates occurrences of 'ANY <sort>' by substituting fresh, free variables.
-- Also returns the previous TorXakis definitions (so that they can be restored afterwards, see above).
eliminateAny :: UndefVExpr -> IOC.IOC (TxsDefs.TxsDefs, UndefVExpr)
eliminateAny (expr, undefs) = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    newExpr <- visitValExprM anyElmVisitorM id buildVExpr expr
    return (tdefs, (newExpr, undefs))
  where
    buildVExpr :: TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
    buildVExpr v = do return v
    
    anyElmVisitorM :: [(TxsDefs.VExpr, Integer)] -> (TxsDefs.VExpr -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr) -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
    anyElmVisitorM subExps _ _ (view -> Vconst (Cany sort)) = do
        do varId <- createFreshVar sort
           return (cstrVar varId)
    anyElmVisitorM subExps g h parentExpr = defaultValExprVisitorM subExps g h parentExpr
-- eliminateAny

-- Applies a substitution to the given expression, introducing 'undefined variables' (as defined above) where necessary.
-- Also returns the previous TorXakis definitions (so that they can be restored afterwards):
doVarSubst :: [(VarId, UndefVExpr)] -> UndefVExpr -> IOC.IOC (TxsDefs.TxsDefs, UndefVExpr)
doVarSubst substEqs (expr, undefs) = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    newExprs <- Monad.mapM eliminateAny (map snd substEqs)
    let newSubstEqs = zip (map fst substEqs) (map snd newExprs)
    (newExpr, newUndefs) <- visitValExprM substVisitor fst buildUndefVExpr expr
    return (tdefs, (newExpr, undefs ++ newUndefs))
  where
    buildUndefVExpr :: TxsDefs.VExpr -> IOC.IOC UndefVExpr
    buildUndefVExpr v = do return (v, [])
    
    substVisitor :: [(UndefVExpr, Integer)] -> (UndefVExpr -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> IOC.IOC UndefVExpr) -> UndefVExpr -> IOC.IOC UndefVExpr
    -- If we find a variable, substitute it (only if it is present in substEqs, of course):
    substVisitor _ _ _ ((view -> Vvar varId), undefs) =
        case [(v, us) | (p, (v, us)) <- substEqs, p == varId] of
          [(v, us)] -> do return (v, undefs ++ us)
          _ -> do return (cstrVar varId, undefs)
    -- An expression that accesses a non-existent field (possible when using an accessor on the wrong constructor sort)
    -- means that we introduce a new 'undefined variable':
    substVisitor [((subExpr@(view -> Vcstr c1 _fields), undefs1), _)] _ _ ((view -> Vaccess c2 p _vexp), undefs2) =
        if c1 == c2
        then do return (cstrAccess c2 p subExpr, undefs1 ++ undefs2)
        else do varId <- createFreshVar ((CstrId.cstrargs c1) !! p)
                return (cstrVar varId, undefs2 ++ [varId])
    -- Constructors exist in constant and non-constant forms.
    -- We do the same here as above, but for the constant form:
    substVisitor [((subExpr@(view -> Vconst (Ccstr c1 _fields)), undefs1), _)] _ _ ((view -> Vaccess c2 p _vexp), undefs2) =
        if c1 == c2
        then do return (cstrAccess c2 p subExpr, undefs1 ++ undefs2)
        else do varId <- createFreshVar ((CstrId.cstrargs c1) !! p)
                return (cstrVar varId, undefs2 ++ [varId])
    -- In other cases, the parent expression inherits undefined variables from its sub-expressions:
    substVisitor subExps g h (parentExpr, undefs) = do
        (parentExpr', undefs') <- defaultValExprVisitorM subExps g h (parentExpr, undefs)
        return (parentExpr', undefs ++ undefs' ++ (concat (map (snd . fst) subExps)))
-- doVarSubst

extractVExprFromSolMap :: VarId -> Map.Map VarId Constant -> Constant
extractVExprFromSolMap varId m = Map.findWithDefault (Cany (SortOf.sortOf varId)) varId m

-- Frequently used method; code is modified code from TxsCore (with several safety checks removed!!).
-- Attempts to find a solution for the given expression.
-- If a solution is found, it consists of a map with one value for each of the specified variables.
getSomeSolution :: UndefVExpr -> [VarId] -> IOC.IOC (SolveDefs.SolveProblem VarId)
getSomeSolution (expr, undefs) variables =
    if SortOf.sortOf expr /= SortId.sortIdBool
    then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Value expression must be of sort Bool (" ++ (show expr) ++ ")!") ]
            return SolveDefs.UnableToSolve
    else do smtEnv <- IOC.getSMT "current"
            (tdefs1, (expr1, undefs1)) <- eliminateAny (expr, undefs)
            let freeVars1 = Set.toList (Set.fromList ((FreeVar.freeVars expr1) ++ variables))
            let assertions1 = Solve.add expr1 Solve.empty
            (sol1, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve freeVars1 assertions1) smtEnv
            case sol1 of
              SolveDefs.Solved solMap ->
                do let freeVars2 = undefs
                   let solvedVars = Set.toList ((Set.fromList freeVars1) Set.\\ (Set.fromList freeVars2))
                   let solvedParamEqs = map (\v -> (v, (extractVExprFromMap v solMap, []))) solvedVars
                   (_, solvedExpr) <- doVarSubst solvedParamEqs (expr1, undefs1)
                   let assertions2 = Solve.add (cstrNot solvedExpr) Solve.empty
                   (sol2, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve freeVars2 assertions2) smtEnv
                   case sol1 of
                     SolveDefs.Unsolvable -> do restoreTdefs tdefs1
                                                return (SolveDefs.Solved (Map.map (\v -> cstrConst (extractVExprFromSolMap v solMap)) variables))
                     _ -> do restoreTdefs tdefs1
                             return SolveDefs.UnableToSolve
              otherResult -> do restoreTdefs tdefs1
                                return otherResult
-- getSomeSolution

-- Checks if the specified expression cannot be false.
isTautology :: UndefVExpr -> IOC.IOC Bool
isTautology (expr, undefs) = isNotSatisfiable ((cstrNot expr), undefs)

-- Checks if the specified expression can be true.
isSatisfiable :: UndefVExpr -> IOC.IOC Bool
isSatisfiable expr = do
    sol <- getSomeSolution expr []
    case sol of
      SolveDefs.Solved _ -> do return True
      _ -> do return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isNotSatisfiable :: UndefVExpr -> IOC.IOC Bool
isNotSatisfiable expr = do
    sol <- getSomeSolution expr []
    return (sol == SolveDefs.UnableToSolve)
-- isNotSatisfiable

-- Checks if all specified expressions could be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, X == 1] would yield true!
areSatisfiable :: [UndefVExpr] -> IOC.IOC Bool
areSatisfiable expressions = do sat <- Monad.mapM isSatisfiable expressions
                                return (List.and sat)
-- areSatisfiable

-- Checks if none of the specified expressions not be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, false] would yield false!
areNotSatisfiable :: [UndefVExpr] -> IOC.IOC Bool
areNotSatisfiable expressions = do sat <- Monad.mapM isNotSatisfiable expressions
                                   return (List.and sat)
-- areNotSatisfiable

-- Attempts to find a unique solution for the given expression.
-- The solution only has to be unique with regard to the variables listed by the third parameter:
getUniqueSolution :: UndefVExpr -> [VarId] -> [VarId] -> IOC.IOC (SolveDefs.SolveProblem VarId)
getUniqueSolution (expr, undefs) variables uniqueSolVars = do
    sol <- getSomeSolution (expr, undefs) variables
    case sol of
      SolveDefs.Solved solMap ->
        do -- Then check if there is NO solution where (one of) the specified variables have different values:
           let extraConditions = map (\v -> cstrEqual (cstrVar v) (extractVExprFromSolMap v solMap)) uniqueSolVars
           let restrictedExpression = (cstrAnd (Set.fromList [expr, cstrNot (cstrAnd (Set.fromList extraConditions))]), undefs)
           unsat <- isNotSatisfiable restrictedExpression
           -- If so, the solution is unique (w.r.t. the specified variables):
           return (if unsat then sol else SolveDefs.UnableToSolve)
      _ -> return sol
-- getUniqueSolution

showSolution :: SolveDefs.SolveProblem VarId -> String
showSolution SolveDefs.Unsolvable = "Unsolvable"
showSolution SolveDefs.UnableToSolve = "UnableToSolve"
showSolution (SolveDefs.Solved solMap) =
    let f (p, v) = (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr (cstrConst v)) in
      "Solved [" ++ (separatedList (map f (Map.toList solMap)) ", ") ++ "]"
  where
    separatedList :: [String] -> String -> String
    separatedList [] _ = ""
    separatedList [x] _ = x
    separatedList (x1:x2:xs) separator = x1 ++ separator ++ (separatedList (x2:xs) separator)
-- showSolution








