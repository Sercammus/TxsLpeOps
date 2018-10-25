{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEClean
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEClean (
cleanLPE
) where

import qualified Data.List           as List
import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified ChanId
import LPEOps
import Satisfiability
import ValExpr
import LPESuccessors

-- Removes duplicate summands and summands that are unreachable by all other (!) summands
-- (so basically we do a partial, symbolic reachability analysis).
cleanLPE :: LPEOperation
cleanLPE (channels, initParamEqs, summands) _out invariant = do
    uniqueSummands <- Monad.foldM addSummandIfUnique [] summands
    predecessorSummands <- Monad.foldM addSummandIfPredecessor [] uniqueSummands
    return (Right (channels, initParamEqs, predecessorSummands))
  where
    addSummandIfUnique :: LPESummands -> LPESummand -> IOC.IOC LPESummands
    addSummandIfUnique soFar candidate = do
        found <- containsSummand soFar invariant candidate
        if found
        then do return soFar
        else do return (candidate:soFar)
    
    addSummandIfPredecessor :: LPESummands -> LPESummand -> IOC.IOC LPESummands
    addSummandIfPredecessor soFar candidate@(LPESummand _channelVars _channelOffers guard _paramEqs) = do
        -- Check if the summand can be reached via the initial state:
        guard' <- doBlindSubst initParamEqs guard
        sat <- isSatisfiable guard' invariant
        if sat
        then do return (candidate:soFar)
        else do -- Check which summands could possible enable this summand:
                predecessors <- getPossiblePredecessors summands invariant candidate
                -- If the summand is only enabled by itself, it can still be safely deleted:
                let predecessorsSet = Set.delete candidate (Set.fromList predecessors)
                if predecessorsSet /= Set.empty
                then do return (candidate:soFar)
                else do return soFar
-- cleanLPE

containsSummand :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
containsSummand [] _ _ = do return False
containsSummand (x:xs) invariant summand = do
    equiv <- isEquivalentSummand x summand invariant
    if equiv
    then do return True
    else containsSummand xs summand
-- containsSummand

isEquivalentSummand :: LPESummand -> LPESummand -> TxsDefs.VExpr -> IOC.IOC Bool
isEquivalentSummand (LPESummand _ _ _ LPEStop) (LPESummand _ _ _ (LPEProcInst _)) _ = do return False
isEquivalentSummand (LPESummand _ _ _ (LPEProcInst _)) (LPESummand _ _ _ LPEStop) _ = do return False
isEquivalentSummand (LPESummand _vars1 chans1 guard1 LPEStop) (LPESummand _vars2 chans2 guard2 LPEStop) invariant = do
    let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
    if (map fst sortedChans1) /= (map fst sortedChans2)
    then do return False
    else do let chanVars1 = concat (map snd sortedChans1)
            let chanVars2 = concat (map snd sortedChans2)
            let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, cstrVar cv1)) chanVars1 chanVars2)
            guard2' <- doBlindSubst subst guard2
            let guardEq = cstrEqual guard1 guard2'
            taut <- isTautology guardEq invariant
            return taut
isEquivalentSummand (LPESummand _vars1 chans1 guard1 (LPEProcInst paramEqs1)) (LPESummand _vars2 chans2 guard2 (LPEProcInst paramEqs2)) invariant = do
    let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
    if (map fst sortedChans1) /= (map fst sortedChans2)
    then do return False
    else do let chanVars1 = concat (map snd sortedChans1)
            let chanVars2 = concat (map snd sortedChans2)
            let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, cstrVar cv1)) chanVars1 chanVars2)
            guard2' <- doBlindSubst subst guard2
            let guardEq = cstrEqual guard1 guard2'
            procInstEqs <- Monad.mapM (getProcInstEq subst) (Map.toList paramEqs1)
            taut <- isTautology (cstrAnd (Set.fromList (guardEq:procInstEqs))) invariant
            return taut
  where
    getProcInstEq :: Map.Map VarId TxsDefs.VExpr -> (VarId, TxsDefs.VExpr) -> IOC.IOC TxsDefs.VExpr
    getProcInstEq subst (p1, v1) = do
        let v2 = paramEqs2 Map.! p1
        v2' <- doBlindSubstr subst v2
        return (cstrEqual v1 (chanVarSubst v2))
-- isEquivalentSummand













