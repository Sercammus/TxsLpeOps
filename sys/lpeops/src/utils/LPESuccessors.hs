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
getDefiniteSuccessors,
getPossibleCoActors
) where

import qualified Data.List           as List
import qualified Data.Map            as Map
import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified ChanId
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           ValExpr hiding (subst)

getPossiblePredecessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossiblePredecessors allSummands invariant (LPESummand _ _ guard _) =
    Monad.foldM addSummandIfPossiblePredecessor [] (Set.toList allSummands)
  where
    addSummandIfPossiblePredecessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfPossiblePredecessor soFar summand@(LPESummand _ _ g paramEqs) = do
        guard' <- doBlindSubst paramEqs guard
        sat <- couldBeSatisfiable (cstrAnd (Set.fromList [g, guard'])) invariant
        return $ if sat then summand:soFar else soFar
-- getPossibleSuccessors

couldHavePredecessor :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
couldHavePredecessor allSummands invariant (LPESummand _ _ guard _) =
    Monad.foldM isPossiblePredecessor False (Set.toList allSummands)
  where
    isPossiblePredecessor :: Bool -> LPESummand -> IOC.IOC Bool
    isPossiblePredecessor soFar (LPESummand _ _ g paramEqs) =
        if soFar
        then return True
        else do guard' <- doBlindSubst paramEqs guard
                couldBeSatisfiable (cstrAnd (Set.fromList [g, guard'])) invariant
-- getPossibleSuccessors

-- Selects all potential successors summands of a given summand from a list with all summands.
-- (In actuality, an overapproximation of all potential successors is selected, namely those
-- whose guard can be satisfied after the guard of the current summand has been satisfied and
-- after the substitutions of the process recursion have taken place.)
getPossibleSuccessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossibleSuccessors allSummands invariant (LPESummand _ _ guard paramEqs) =
    Monad.foldM addSummandIfPossibleSuccessor [] (Set.toList allSummands)
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
getDefiniteSuccessors allSummands invariant (LPESummand _ _ guard paramEqs) =
    Monad.filterM isDefiniteSuccessor (Set.toList allSummands)
  where
    isDefiniteSuccessor :: LPESummand -> IOC.IOC Bool
    isDefiniteSuccessor (LPESummand _ _ g _) = do
        g' <- doBlindSubst paramEqs g
        isTautology (cstrAnd (Set.fromList [guard, g'])) invariant
-- getDefiniteSuccessors

-- Selects all summands from a given list that could generate the same action (both label and arguments) at the same time.
-- The result is an overapproximation!
getPossibleCoActors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossibleCoActors allSummands invariant (LPESummand _ chans1 guard1 _) =
    Monad.filterM isPossibleCoActor (Set.toList allSummands)
  where
    isPossibleCoActor :: LPESummand -> IOC.IOC Bool
    isPossibleCoActor (LPESummand _ chans2 guard2 _) = do
        let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
        let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
        -- All action labels must be the same (order does not matter, because we sorted):
        if map fst sortedChans1 /= map fst sortedChans2
        then return False
        else do -- Both guards must be able to be true at the same time:
                let guards = cstrAnd (Set.fromList [guard1, guard2])
                notSat <- isNotSatisfiable guards invariant
                if notSat
                then return False
                else do -- All action arguments must be able to have the same value.
                        -- To check this, substitute the (by definition fresh) channel variables of one summand into the other:
                        let chanVars1 = concatMap snd sortedChans1
                        let chanVars2 = concatMap snd sortedChans2
                        let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
                        guard2' <- doBlindSubst subst guard2
                        let guardEq = ValExpr.cstrEqual guard1 guard2'
                        isSatisfiable guardEq invariant
-- getPossibleCoActors












