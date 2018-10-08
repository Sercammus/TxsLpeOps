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
showSolution,
createVarSubst,
varSubst
) where

import Control.Monad.State
import qualified Control.Monad as Monad
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

-- Checks if the specified expression cannot be false.
isTautology :: TxsDefs.VExpr -> IOC.IOC Bool
isTautology expression = isNotSatisfiable (cstrNot expression)

-- Checks if the specified expression can be true.
isSatisfiable :: TxsDefs.VExpr -> IOC.IOC Bool
isSatisfiable expression = do sat <- getSat expression
                              case sat of
                                SolveDefs.Sat -> return True
                                _ -> return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isNotSatisfiable :: TxsDefs.VExpr -> IOC.IOC Bool
isNotSatisfiable expression = do sat <- getSat expression
                                 case sat of
                                   SolveDefs.Unsat -> return True
                                   _ -> return False
-- isNotSatisfiable

-- Checks if all specified expressions can be true (when considered separately.
areSatisfiable :: [TxsDefs.VExpr] -> IOC.IOC Bool
areSatisfiable expressions = do sat <- Monad.mapM isSatisfiable expressions
                                return (List.all (\s -> s) sat)
-- areSatisfiable

-- Checks if the specified expression cannot be true.
areNotSatisfiable :: [TxsDefs.VExpr] -> IOC.IOC Bool
areNotSatisfiable expressions = do sat <- Monad.mapM isNotSatisfiable expressions
                                   return (List.all (\s -> s) sat)
-- areNotSatisfiable

-- Frequently used method; code is modified code from TxsCore.
-- Checks whether the given expression is satisfiable.
getSat :: TxsDefs.VExpr -> IOC.IOC SolveDefs.SolvableProblem
getSat expression = do
    envc <- get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'satsolve' without model" ]
                       return SolveDefs.Unknown
      _ -> if SortOf.sortOf expression /= SortId.sortIdBool
           then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "Value expression shall be Bool" ]
                   return SolveDefs.Unknown
           else do expr <- anyElm expression
                   let frees = FreeVar.freeVars expr
                   let assertions = Solve.add expr Solve.empty
                   smtEnv <- IOC.getSMT "current"
                   case smtEnv of
                     SMTData.SmtEnvError -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Could not locate SMT solver" ]
                                               return SolveDefs.Unknown
                     _ -> if Solve.isEasySolve frees assertions
                          then do (sat, smtEnv') <- lift $ runStateT (Solve.satSolve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  return sat
                          else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
                                  (sat, smtEnv') <- lift $ runStateT (Solve.satSolve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> " ++ (show sat)) ]
                                  IOC.putSMT "current" smtEnv'
                                  return sat
-- getSat

-- Frequently used method; code is modified code from TxsCore.
-- Attempts to find a solution for the given expression.
getSomeSolution :: TxsDefs.VExpr -> [VarId] -> IOC.IOC (Maybe (Map.Map VarId TxsDefs.VExpr))
getSomeSolution expression variables = do
    envc <- get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'solve' without model" ]
                       return Nothing
      _ -> if SortOf.sortOf expression /= SortId.sortIdBool
           then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "Value expression shall be Bool" ]
                   return Nothing
           else do expr <- anyElm expression
                   let frees = Set.toList (Set.fromList ((FreeVar.freeVars expr) ++ variables))
                   let assertions = Solve.add expr Solve.empty
                   smtEnv <- IOC.getSMT "current"
                   case smtEnv of
                     SMTData.SmtEnvError -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Could not locate SMT solver" ]
                                               return Nothing
                     _ -> if Solve.isEasySolve frees assertions
                          then do (sol, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (Map.map cstrConst solMap))
                                    _ -> return Nothing
                          else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
                                  (sol, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> " ++ (showSolution sol)) ]
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (Map.map cstrConst solMap))
                                    _ -> return Nothing
-- getSomeSolution

-- Attempts to find a unique solution for the given expression.
-- The solution only has to be unique with regard to the variables listed by the third parameter:
getUniqueSolution :: TxsDefs.VExpr -> [VarId] -> [VarId] -> IOC.IOC (Maybe (Map.Map VarId TxsDefs.VExpr))
getUniqueSolution expression variables uniquelySolvedVars = do
    -- Start by finding some arbitrary solution:
    expressionWithoutAny <- anyElm expression
    someSolution <- getSomeSolution expressionWithoutAny variables
    case someSolution of
      Just solMap -> do -- Then check if there is NO solution where (one of) the specified variables have different values:
                        let extraConditions = map (\v -> cstrEqual (cstrVar v) (extractVExprFromMap v solMap)) uniquelySolvedVars
                        let restrictedExpression = cstrAnd (Set.fromList [expressionWithoutAny, cstrNot (cstrAnd (Set.fromList extraConditions))])
                        unsat <- isNotSatisfiable restrictedExpression
                        -- If so, the solution is unique (w.r.t. the specified variables):
                        return (if unsat then someSolution else Nothing)
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

-- Eliminates occurrences of ANY by substituting them for fresh, free variables.
anyElm :: TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
anyElm expr = visitValExpr anyElmVisitorM expr
  where
    anyElmVisitorM :: [(IOC.IOC TxsDefs.VExpr, Integer)] -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
    anyElmVisitorM _ (view -> Vconst (Cany sort)) = do varId <- createFreshVar sort
                                                       return (cstrVar varId)
    anyElmVisitorM vexps parentExpr = defaultValExprVisitorM vexps parentExpr
-- anyElm

createVarSubst :: [(VarId, TxsDefs.VExpr)] -> (TxsDefs.VExpr -> TxsDefs.VExpr)
createVarSubst substEqs e = varSubst substEqs (e :: TxsDefs.VExpr)

-- Substitutes variables in a boolean expression while avoiding invalid subexpressions.
-- This is useful when substituting into expressions that will be SAT-checked:
varSubst :: [(VarId, TxsDefs.VExpr)] -> TxsDefs.VExpr -> TxsDefs.VExpr
varSubst substEqs expr =
    let (valid, result) = visitValExpr validityVisitor expr in
      if valid
      then result
      else cstrConst (Cbool False)
  where
    -- The first element of the pair is the condition under which the second element is a DEFINED value.
    -- We abbreviate this with dc, for 'defined condition'.
    validityVisitor :: [((Bool, TxsDefs.VExpr), Integer)] -> TxsDefs.VExpr -> (Bool, TxsDefs.VExpr)
    validityVisitor _ (view -> Vvar varId) =
         -- Perform the substitution:
        case [v | (p, v) <- substEqs, p == varId] of
          [v] -> (True, v)
          _ -> (True, cstrVar varId)
    validityVisitor [((valid, cstrExpr@(view -> Vconst (Ccstr c2 _fields))), _)] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if c1 == c2
        then (valid, cstrAccess c1 p cstrExpr)
        else (False, cstrConst (Cany (CstrId.cstrsort c1)))
    validityVisitor [((valid, cstrExpr@(view -> Vcstr c2 _fields)), _)] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if (c1 == c2)
        then (valid, cstrAccess c1 p cstrExpr)
        else (False, cstrConst (Cany (CstrId.cstrsort c1)))
    validityVisitor vexps parentExpr =
        -- Usually, the parent expression is unsatisfiable if the children are unsatisfiable:
        (combineValidity (map fst vexps), defaultValExprVisitor (map (\((_, v), k) -> (v, k)) vexps) parentExpr)
    -- validityVisitor
    
    combineValidity :: [(Bool, TxsDefs.VExpr)] -> Bool
    combineValidity [] = True
    combineValidity [(valid, _)] = valid
    combineValidity ((valid, _):xs) = valid && (combineValidity xs)
-- varSubst


