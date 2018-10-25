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
module BlindSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified EnvData
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified FreeVar
import qualified Solve
import qualified SortId
import qualified SortOf
import VarId
import ValExpr
import BlindSubst

-- Frequently used method; code is modified code from TxsCore (with several safety checks removed!!).
-- Attempts to find a solution for the given expression.
-- If a solution is found, it consists of a map with one value for each of the specified variables.
getSomeSolution :: BlindValExpr -> [VarId] -> IOC.IOC BlindSolution
getSomeSolution (expr, undefs) variables =
    if SortOf.sortOf expr /= SortId.sortIdBool
    then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Value expression must be of sort Bool (" ++ (show expr) ++ ")!") ]
            return UnableToSolve
    else do smtEnv <- IOC.getSMT "current"
            (tdefs1, (expr1, undefs1)) <- eliminateAny (expr, undefs)
            let freeVars1 = Set.fromList ((FreeVar.freeVars expr1) ++ variables)
            let assertions1 = Solve.add expr1 Solve.empty
            (sol1, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve (Set.toList freeVars1) assertions1) smtEnv
            case toBlindSolution sol1 of
              Solution solMap ->
                do let freeVars2 = undefs
                   let blindSubstVars = Set.toList (freeVars1 Set.\\ freeVars2)
                   let blindSubst = Map.fromList (map (\v -> (v, lookupBlindValExpr v solMap)) blindSubstVars)
                   (_, (blindSubstExpr, _)) <- doBlindSubst blindSubst (expr1, undefs1)
                   let assertions2 = Solve.add (cstrNot blindSubstExpr) Solve.empty
                   (sol2, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve (Set.toList freeVars2) assertions2) smtEnv
                   case toBlindSolution sol2 of
                     Unsolvable -> do restoreTdefs tdefs1
                                      return (Solution (Map.fromList (map (\v -> (v, lookupBlindValExpr v solMap)) variables)))
                     _ -> do restoreTdefs tdefs1
                             return UnableToSolve
              otherResult -> do restoreTdefs tdefs1
                                return otherResult
-- getSomeSolution

-- Checks if the specified expression cannot be false.
isTautology :: BlindValExpr -> IOC.IOC Bool
isTautology (expr, undefs) = isNotSatisfiable ((cstrNot expr), undefs)

-- Checks if the specified expression can be true.
isSatisfiable :: BlindValExpr -> IOC.IOC Bool
isSatisfiable expr = do
    sol <- getSomeSolution expr []
    case sol of
      Solution _ -> do return True
      _ -> do return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isNotSatisfiable :: BlindValExpr -> IOC.IOC Bool
isNotSatisfiable expr = do
    sol <- getSomeSolution expr []
    return (sol == UnableToSolve)
-- isNotSatisfiable

-- Checks if all specified expressions could be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, X == 1] would yield true!
areSatisfiable :: [BlindValExpr] -> IOC.IOC Bool
areSatisfiable expressions = do sat <- Monad.mapM isSatisfiable expressions
                                return (List.and sat)
-- areSatisfiable

-- Checks if none of the specified expressions not be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, false] would yield false!
areNotSatisfiable :: [BlindValExpr] -> IOC.IOC Bool
areNotSatisfiable expressions = do sat <- Monad.mapM isNotSatisfiable expressions
                                   return (List.and sat)
-- areNotSatisfiable

-- Attempts to find a unique solution for the given expression.
-- The solution only has to be unique with regard to the variables listed by the third parameter:
getUniqueSolution :: BlindValExpr -> [VarId] -> [VarId] -> IOC.IOC BlindSolution
getUniqueSolution (expr, undefs) variables uniqueSolVars = do
    sol <- getSomeSolution (expr, undefs) variables
    case sol of
      Solution solMap ->
        do -- Then check if there is NO solution where (one of) the specified variables have different values:
           let extraConditions = map (\v -> cstrEqual (cstrVar v) (fst (lookupBlindValExpr v solMap))) uniqueSolVars
           let extraUndefs = Set.unions (map (\v -> (snd (lookupBlindValExpr v solMap))) uniqueSolVars)
           let restrictedExpression = (cstrAnd (Set.fromList [expr, cstrNot (cstrAnd (Set.fromList extraConditions))]), Set.union undefs extraUndefs)
           unsat <- isNotSatisfiable restrictedExpression
           -- If so, the solution is unique (w.r.t. the specified variables):
           return (if unsat then sol else UnableToSolve)
      _ -> return sol
-- getUniqueSolution

-- showSolution :: SolveDefs.SolveProblem VarId -> String
-- showSolution SolveDefs.Unsolvable = "Unsolvable"
-- showSolution SolveDefs.UnableToSolve = "UnableToSolve"
-- showSolution (SolveDefs.Solved solMap) =
    -- let f (p, v) = (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr (cstrConst v)) in
      -- "Solved [" ++ (separatedList (map f (Map.toList solMap)) ", ") ++ "]"
  -- where
    -- separatedList :: [String] -> String -> String
    -- separatedList [] _ = ""
    -- separatedList [x] _ = x
    -- separatedList (x1:x2:xs) separator = x1 ++ separator ++ (separatedList (x2:xs) separator)
-- -- showSolution








