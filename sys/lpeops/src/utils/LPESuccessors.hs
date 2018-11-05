{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPESuccessors
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPESuccessors (
getPossiblePredecessors,
couldHavePredecessor,
getPossibleSuccessors,
getDefiniteSuccessors
) where

import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           ValExpr

getPossiblePredecessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossiblePredecessors allSummands invariant (LPESummand _channelVars _channelOffers guard _procInst) = do
    predecessors <- Monad.foldM addSummandIfPossiblePredecessor [] (Set.toList allSummands)
    return $ predecessors
  where
    addSummandIfPossiblePredecessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfPossiblePredecessor soFar (LPESummand _ _ _ LPEStop) = do return soFar
    addSummandIfPossiblePredecessor soFar summand@(LPESummand _ _ g (LPEProcInst paramEqs)) = do
        guard' <- doBlindSubst paramEqs guard
        sat <- couldBeSatisfiable (cstrAnd (Set.fromList [g, guard'])) invariant
        return $ if sat then summand:soFar else soFar
-- getPossibleSuccessors

couldHavePredecessor :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
couldHavePredecessor allSummands invariant (LPESummand _channelVars _channelOffers guard _procInst) = do
    Monad.foldM isPossiblePredecessor False (Set.toList allSummands)
  where
    isPossiblePredecessor :: Bool -> LPESummand -> IOC.IOC Bool
    isPossiblePredecessor soFar (LPESummand _ _ _ LPEStop) = do return soFar
    isPossiblePredecessor soFar (LPESummand _ _ g (LPEProcInst paramEqs)) = do
        if soFar
        then do return True
        else do guard' <- doBlindSubst paramEqs guard
                couldBeSatisfiable (cstrAnd (Set.fromList [g, guard'])) invariant
-- getPossibleSuccessors

-- Selects all potential successors summands of a given summand from a list with all summands.
-- (In actuality, an overapproximation of all potential successors is selected, namely those
-- whose guard can be satisfied after the guard of the current summand has been satisfied and
-- after the substitutions of the process recursion have taken place.)
getPossibleSuccessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossibleSuccessors _ _ (LPESummand _ _ _ LPEStop) = do return []
getPossibleSuccessors allSummands invariant (LPESummand _channelVars _channelOffers guard (LPEProcInst paramEqs)) = do
    successors <- Monad.foldM addSummandIfPossibleSuccessor [] (Set.toList allSummands)
    return $ successors
  where
    addSummandIfPossibleSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfPossibleSuccessor soFar summand@(LPESummand _ _ g _) = do
        g' <- doBlindSubst paramEqs g
        sat <- couldBeSatisfiable (cstrAnd (Set.fromList [guard, g'])) invariant
        return $ if sat then soFar ++ [summand] else soFar
-- getPossibleSuccessors

-- Selects all summands from a given list that are definitely successors of a given summand.
-- The result is an underapproximation!
getDefiniteSuccessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getDefiniteSuccessors _ _ (LPESummand _ _ _ LPEStop) = do return []
getDefiniteSuccessors allSummands invariant (LPESummand _channelVars _channelOffers guard (LPEProcInst paramEqs)) = do
    successors <- Monad.foldM addSummandIfDefiniteSuccessor [] (Set.toList allSummands)
    return $ successors
  where
    addSummandIfDefiniteSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfDefiniteSuccessor soFar summand@(LPESummand _ _ g _) = do
        g' <- doBlindSubst paramEqs g
        taut <- isTautology (cstrAnd (Set.fromList [guard, g'])) invariant
        return $ if taut then soFar ++ [summand] else soFar
-- getDefiniteSuccessors

