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
import ValExprVisitor
import VarFactory
import ValFactory

-- Checks if the specified expression cannot be false.
isTautology :: TxsDefs.VExpr -> IOC.IOC Bool
isTautology expression = isNotSatisfiable (cstrNot expression)

-- Checks if the specified expression can be true.
isSatisfiable :: TxsDefs.VExpr -> IOC.IOC Bool
isSatisfiable expression = do (tdefs, expr) <- eliminateAny expression
                              sat <- getSat expr
                              restoreTdefs tdefs
                              case sat of
                                SolveDefs.Sat -> return True
                                _ -> return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isNotSatisfiable :: TxsDefs.VExpr -> IOC.IOC Bool
isNotSatisfiable expression = do (tdefs, expr) <- eliminateAny expression
                                 sat <- getSat expr
                                 restoreTdefs tdefs
                                 case sat of
                                   SolveDefs.Unsat -> return True
                                   _ -> return False
-- isNotSatisfiable

-- Checks if all specified expressions could be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, X == 1] would yield true!
areSatisfiable :: [TxsDefs.VExpr] -> IOC.IOC Bool
areSatisfiable expressions = do sat <- Monad.mapM isSatisfiable expressions
                                return (List.and sat)
-- areSatisfiable

-- Checks if none of the specified expressions not be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, X == 1, false] would yield false!
areNotSatisfiable :: [TxsDefs.VExpr] -> IOC.IOC Bool
areNotSatisfiable expressions = do sat <- Monad.mapM isNotSatisfiable expressions
                                   return (List.and sat)
-- areNotSatisfiable

-- Frequently used method; code is modified code from TxsCore.
-- Checks whether the given expression is satisfiable.
getSat :: TxsDefs.VExpr -> IOC.IOC SolveDefs.SolvableProblem
getSat expression = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'satsolve' without model" ]
                       return SolveDefs.Unknown
      _ -> if SortOf.sortOf expression /= SortId.sortIdBool
           then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "Value expression shall be Bool" ]
                   return SolveDefs.Unknown
           else do let frees = FreeVar.freeVars expression
                   let assertions = Solve.add expression Solve.empty
                   smtEnv <- IOC.getSMT "current"
                   case smtEnv of
                     SMTData.SmtEnvError -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Could not locate SMT solver" ]
                                               return SolveDefs.Unknown
                     _ -> if Solve.isEasySolve frees assertions
                          then do (sat, smtEnv') <- MonadState.lift $ MonadState.runStateT (Solve.satSolve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  return sat
                          else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expression) ++ " ==> ?") ]
                                  (sat, smtEnv') <- MonadState.lift $ MonadState.runStateT (Solve.satSolve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expression) ++ " ==> " ++ (show sat)) ]
                                  IOC.putSMT "current" smtEnv'
                                  return sat
-- getSat

-- Frequently used method; code is modified code from TxsCore.
-- Attempts to find a solution for the given expression.
getSomeSolution :: TxsDefs.VExpr -> [VarId] -> IOC.IOC (Maybe (TxsDefs.TxsDefs, Map.Map VarId TxsDefs.VExpr))
getSomeSolution expression variables = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'solve' without model" ]
                       return Nothing
      _ -> if SortOf.sortOf expression /= SortId.sortIdBool
           then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "Value expression shall be Bool" ]
                   return Nothing
           else do (tdefs, expr) <- eliminateAny expression
                   let frees = Set.toList (Set.fromList ((FreeVar.freeVars expr) ++ variables))
                   let assertions = Solve.add expr Solve.empty
                   smtEnv <- IOC.getSMT "current"
                   case smtEnv of
                     SMTData.SmtEnvError -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Could not locate SMT solver" ]
                                               return Nothing
                     _ -> if Solve.isEasySolve frees assertions
                          then do (sol, smtEnv') <- MonadState.lift $ MonadState.runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (tdefs, Map.map cstrConst solMap))
                                    _ -> return Nothing
                          else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
                                  (sol, smtEnv') <- MonadState.lift $ MonadState.runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> " ++ (showSolution sol)) ]
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (tdefs, Map.map cstrConst solMap))
                                    _ -> return Nothing
-- getSomeSolution

-- Attempts to find a unique solution for the given expression.
-- The solution only has to be unique with regard to the variables listed by the third parameter:
getUniqueSolution :: TxsDefs.VExpr -> [VarId] -> [VarId] -> IOC.IOC (Maybe (TxsDefs.TxsDefs, Map.Map VarId TxsDefs.VExpr))
getUniqueSolution expression variables uniquelySolvedVars = do
    -- Start by finding some arbitrary solution:
    (tdefs, expressionWithoutAny) <- eliminateAny expression
    someSolution <- getSomeSolution expressionWithoutAny variables
    case someSolution of
      Just (_, solMap) -> do -- Then check if there is NO solution where (one of) the specified variables have different values:
                             let extraConditions = map (\v -> cstrEqual (cstrVar v) (extractVExprFromMap v solMap)) uniquelySolvedVars
                             let restrictedExpression = cstrAnd (Set.fromList [expressionWithoutAny, cstrNot (cstrAnd (Set.fromList extraConditions))])
                             unsat <- isNotSatisfiable restrictedExpression
                             -- If so, the solution is unique (w.r.t. the specified variables):
                             return (if unsat then Just (tdefs, solMap) else Nothing)
      _ -> return Nothing
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

restoreTdefs :: TxsDefs.TxsDefs -> IOC.IOC ()
restoreTdefs tdefs = do
    state <- MonadState.gets IOC.state
    let newState = state { IOC.tdefs = tdefs }
    MonadState.modify (\env -> env { IOC.state = newState })
-- restoreTdefs

-- Eliminates occurrences of ANY by substituting them for fresh, free variables.
-- Returns the current 
eliminateAny :: TxsDefs.VExpr -> IOC.IOC (TxsDefs.TxsDefs, TxsDefs.VExpr)
eliminateAny expr = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    newExpr <- visitValExpr anyElmVisitorM expr
    return (tdefs, newExpr)
  where
    anyElmVisitorM :: [(IOC.IOC TxsDefs.VExpr, Integer)] -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
    anyElmVisitorM _ (view -> Vconst (Cany sort)) = do varId <- createFreshVar sort
                                                       return (cstrVar varId)
    anyElmVisitorM vexps parentExpr = defaultValExprVisitorM vexps parentExpr
-- eliminateAny

doVarSubst :: [(VarId, TxsDefs.VExpr)] -> TxsDefs.VExpr -> IOC.IOC (TxsDefs.TxsDefs, TxsDefs.VExpr)
doVarSubst substEqs expr = do
    (tdefs, vs) <- createVarSubst substEqs
    return (tdefs, vs expr)
-- doVarSubst

createVarSubst :: [(VarId, TxsDefs.VExpr)] -> IOC.IOC (TxsDefs.TxsDefs, TxsDefs.VExpr -> TxsDefs.VExpr)
createVarSubst substEqs = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    newExprs <- Monad.mapM eliminateAny (map snd substEqs)
    let newSubstEqs = zip (map fst substEqs) (map snd newExprs)
    tdefs' <- MonadState.gets (IOC.tdefs . IOC.state)
    return (tdefs, varSubst tdefs' newSubstEqs)
-- createVarSubst

-- Substitutes variables in a boolean expression while avoiding invalid subexpressions.
-- This is useful when substituting into expressions that will be SAT-checked:
varSubst :: TxsDefs.TxsDefs -> [(VarId, TxsDefs.VExpr)] -> TxsDefs.VExpr -> TxsDefs.VExpr
varSubst tdefs substEqs expr =
    let (valid, result) = visitValExpr substVisitor expr in
      if valid
      then result
      else (cstrConst (Cbool False))
  where
    substVisitor :: [((Bool, TxsDefs.VExpr), Integer)] -> TxsDefs.VExpr -> (Bool, TxsDefs.VExpr)
    -- If we find a variable, substitute it (only if it is present in substEqs, of course):
    substVisitor _ (view -> Vvar varId) =
        case [v | (p, v) <- substEqs, p == varId] of
          [v] -> (True, v)
          _ -> (True, cstrVar varId)
    -- An expression that accesses a non-existent field (possible when using an accessor on the wrong constructor sort)
    -- means that we substitute a default value (we *have* to give back something).
    -- Furthermore, the entire equation is marked as unsatisfiable:
    substVisitor [((valid, subExpr@(view -> Vcstr c2 _fields)), _)] (view -> Vaccess c1 p _vexp) =
        if c1 == c2
        then (valid, cstrAccess c1 p subExpr)
        else (False, sort2defaultValue tdefs ((CstrId.cstrargs c1) !! p))
    -- Constructors exist in constant and non-constant forms.
    -- We do the same here as above, but for the constant form:
    substVisitor [((valid, subExpr@(view -> Vconst (Ccstr c2 _fields))), _)] (view -> Vaccess c1 p _vexp) =
        if c1 == c2
        then (valid, cstrAccess c1 p subExpr)
        else (False, sort2defaultValue tdefs ((CstrId.cstrargs c1) !! p))
    -- In other cases, the parent expression is unsatisfiable if the children are unsatisfiable:
    substVisitor vexps parentExpr =
        let fsts = map fst vexps in
        let params = zip (map snd fsts) (map snd vexps) in
          (List.and (map fst fsts), defaultValExprVisitor params parentExpr)
-- varSubst


