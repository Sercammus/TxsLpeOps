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
getSomeSolution,
isTautology,
isSatisfiable,
isNotSatisfiable,
areSatisfiable,
areNotSatisfiable,
getUniqueSolution,
showSolution,
defaultInvariant,
module BlindSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified EnvData
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified FreeVar
import qualified Solve
import qualified SortId
import qualified SortOf
import qualified SolveDefs
import qualified TxsDefs
import qualified Constant
import VarId
import ValExpr
import BlindSubst
import LPEPrettyPrint

-- Frequently used method; code is modified code from TxsCore (with several safety checks removed!!).
-- Attempts to find a solution for the given expression.
-- If a solution is found, it consists of a map with one value for each of the specified variables.
getSomeSolution :: TxsDefs.VExpr -> TxsDefs.VExpr -> [VarId] -> IOC.IOC (SolveDefs.SolveProblem VarId)
getSomeSolution expr _invariant variables =
    if SortOf.sortOf expr /= SortId.sortIdBool
    then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Value expression must be of sort Bool (" ++ (show expr) ++ ")!") ]
            return SolveDefs.UnableToSolve
    else do smtEnv <- IOC.getSMT "current"
            (tdefs, expr1, undefs) <- eliminateAny expr
            IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Without ANY *: " ++ (showValExpr expr1)) ]
            IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Undefined variables: " ++ (show undefs)) ]
            let freeVars1 = Set.union (Set.fromList ((FreeVar.freeVars expr1) ++ variables)) undefs
            IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Free variables: " ++ (show freeVars1)) ]
            let assertions1 = Solve.add expr1 Solve.empty
            (sol1, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve (Set.toList freeVars1) assertions1) smtEnv
            IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Solution 1: " ++ (showSolution sol1)) ]
            case sol1 of
              SolveDefs.Solved solMap ->
                do let freeVars2 = undefs
                   let blindSubstVars = Set.toList (freeVars1 Set.\\ freeVars2)
                   let blindSubst = Map.fromList (map (\v -> (v, cstrConst (solMap Map.! v))) blindSubstVars)
                   IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Blind substitution: " ++ (showSubst blindSubst)) ]
                   expr2 <- doBlindSubst blindSubst expr1
                   IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Expression 2: " ++ (showValExpr expr2)) ]
                   let assertions2 = Solve.add (cstrNot expr2) Solve.empty
                   (sol2, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve (Set.toList freeVars2) assertions2) smtEnv
                   IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Solution 2: " ++ (showSolution sol2)) ]
                   case sol2 of
                     SolveDefs.Unsolvable -> do restoreTdefs tdefs
                                                return (SolveDefs.Solved (Map.fromList (map (\v -> (v, solMap Map.! v)) variables)))
                     _ -> do restoreTdefs tdefs
                             return SolveDefs.UnableToSolve
              otherResult -> do restoreTdefs tdefs
                                return otherResult
-- getSomeSolution

defaultInvariant :: TxsDefs.VExpr
defaultInvariant = cstrConst (Constant.Cbool True)

-- Checks if the specified expression cannot be false.
isTautology :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
isTautology expr invariant = do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Tautology? -> " ++ (showValExpr expr)) ]
                                isNotSatisfiable (cstrNot expr) invariant

-- Checks if the specified expression can be true.
isSatisfiable :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
isSatisfiable expr invariant = do
    sol <- getSomeSolution expr invariant []
    case sol of
      SolveDefs.Solved _ -> do return True
      _ -> do return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isNotSatisfiable :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
isNotSatisfiable expr invariant = do
    sol <- getSomeSolution expr invariant []
    return (sol == SolveDefs.Unsolvable)
-- isNotSatisfiable

-- Checks if all specified expressions could be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, X == 1] would yield true!
areSatisfiable :: [TxsDefs.VExpr] -> TxsDefs.VExpr -> IOC.IOC Bool
areSatisfiable expressions invariant = do sat <- Monad.mapM (\e -> isSatisfiable e invariant) expressions
                                          return (List.and sat)
-- areSatisfiable

-- Checks if none of the specified expressions not be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, false] would yield false!
areNotSatisfiable :: [TxsDefs.VExpr] -> TxsDefs.VExpr -> IOC.IOC Bool
areNotSatisfiable expressions invariant = do sat <- Monad.mapM (\e -> isNotSatisfiable e invariant) expressions
                                             return (List.and sat)
-- areNotSatisfiable

-- Attempts to find a unique solution for the given expression.
-- The solution only has to be unique with regard to the variables listed by the third parameter:
getUniqueSolution :: TxsDefs.VExpr -> TxsDefs.VExpr -> [VarId] -> [VarId] -> IOC.IOC (SolveDefs.SolveProblem VarId)
getUniqueSolution expr invariant variables uniqueSolVars = do
    sol <- getSomeSolution expr invariant variables
    case sol of
      SolveDefs.Solved solMap ->
        do -- Then check if there is NO solution where (one of) the specified variables have different values:
           let extraConditions = map (\v -> cstrEqual (cstrVar v) (cstrConst (solMap Map.! v))) uniqueSolVars
           let restrictedExpression = cstrAnd (Set.fromList [expr, cstrNot (cstrAnd (Set.fromList extraConditions))])
           unsat <- isNotSatisfiable restrictedExpression invariant
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








