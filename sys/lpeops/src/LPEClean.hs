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
cleanLPE,
containsSummand
) where

import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified Data.List as List
import qualified Data.Set as Set
import qualified ChanId
import LPEOps
import Satisfiability
import ValExpr

cleanLPE :: LPEOperation
cleanLPE (channels, paramEqs, summands) invariant = do
    uniqueSummands <- Monad.foldM addSummandIfUnique [] summands
    satGuardSummands <- Monad.foldM addSummandIfSatGuard [] uniqueSummands
    return (Left (channels, paramEqs, satGuardSummands))
  where
    addSummandIfUnique :: LPESummands -> LPESummand -> IOC.IOC LPESummands
    addSummandIfUnique soFar candidate = do
      found <- containsSummand soFar candidate
      if found
      then do return soFar
      else do return (candidate:soFar)
    
    addSummandIfSatGuard :: LPESummands -> LPESummand -> IOC.IOC LPESummands
    addSummandIfSatGuard soFar candidate@(LPESummand _channelOffers guard _paramEqs) = do
      sat <- isSatisfiable (cstrAnd (Set.fromList [invariant, guard]))
      if sat
      then do return (candidate:soFar)
      else do return soFar
-- cleanLPE

containsSummand :: LPESummands -> LPESummand -> IOC.IOC Bool
containsSummand [] _ = do return False
containsSummand (x:xs) summand = do
    equiv <- isEquivalentSummand x summand
    if equiv
    then do return True
    else containsSummand xs summand
-- containsSummand

isEquivalentSummand :: LPESummand -> LPESummand -> IOC.IOC Bool
isEquivalentSummand (LPESummand _ _ LPEStop) (LPESummand _ _ (LPEProcInst _)) = do return False
isEquivalentSummand (LPESummand _ _ (LPEProcInst _)) (LPESummand _ _ LPEStop) = do return False
isEquivalentSummand (LPESummand chans1 guard1 LPEStop) (LPESummand chans2 guard2 LPEStop) = do
    let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
    if (map fst sortedChans1) /= (map fst sortedChans2)
    then do return False
    else do let chanVars1 = foldl (++) [] (map snd sortedChans1)
            let chanVars2 = foldl (++) [] (map snd sortedChans2)
            let chanVarSubst = createVarSubst (zipWith (\cv1 cv2 -> (cv2, cstrVar cv1)) chanVars1 chanVars2)
            let guardEq = cstrEqual guard1 (chanVarSubst guard2)
            taut <- isTautology guardEq
            return taut
isEquivalentSummand (LPESummand chans1 guard1 (LPEProcInst paramEqs1)) (LPESummand chans2 guard2 (LPEProcInst paramEqs2)) = do
    let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
    if (map fst sortedChans1) /= (map fst sortedChans2)
    then do return False
    else do let chanVars1 = foldl (++) [] (map snd sortedChans1)
            let chanVars2 = foldl (++) [] (map snd sortedChans2)
            let chanVarSubst = createVarSubst (zipWith (\cv1 cv2 -> (cv2, cstrVar cv1)) chanVars1 chanVars2)
            let guardEq = cstrEqual guard1 (chanVarSubst guard2)
            let procInstEqs = zipWith (\(_, v1) (_, v2) -> cstrEqual v1 (chanVarSubst v2)) paramEqs1 paramEqs2
            taut <- isTautology (cstrAnd (Set.fromList (guardEq:procInstEqs)))
            return taut
-- isEquivalentSummand













