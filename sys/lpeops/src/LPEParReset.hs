{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParReset
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParReset (
parReset
) where

import qualified Control.Monad       as Monad
import qualified Data.List           as List
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified FreeVar
import           LPEOps
import           Satisfiability
import           VarId
import           ValExpr

-- LPE rewrite method.
-- Eliminates parameters that do not contribute to the behavior of a process from an LPE.
-- State spaces before and after are isomorph.
parReset :: LPEOperation
parReset lpeInstance@((_channels, paramEqs, summands)) = do
    immediateSuccessors <- Monad.mapM (getImmediateSuccessors summands) summands
    let successorsPerSummand = zipWith (\s i -> (s, i, map fst paramEqs)) summands immediateSuccessors
    newLPEInstance <- parResetLoop lpeInstance successorsPerSummand
    return (Just newLPEInstance)
-- parReset

getImmediateSuccessors :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
getImmediateSuccessors _ LPEStopSummand = do return []
getImmediateSuccessors allSummands (LPESummand _channelOffers _guard paramEqs) = do
    immediateSuccessors <- Monad.foldM addSummandIfImmediateSuccessor [] allSummands
    return $ immediateSuccessors
  where
    getInstantiationEq :: ValExpr VarId
    getInstantiationEq = cstrAnd (Set.fromList (map (\(p, v) -> cstrEqual (cstrVar p) v) paramEqs))
    
    addSummandIfImmediateSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfImmediateSuccessor soFar summand@(LPESummand _ g _) = do
      sat <- isSatisfiable (cstrAnd (Set.fromList [getInstantiationEq, g]))
      return $ if sat then soFar ++ [summand] else soFar
    addSummandIfImmediateSuccessor soFar _ = do return soFar
-- getImmediateSuccessors 

parResetLoop :: LPEInstance -> [(LPESummand, [LPESummand], [VarId])] -> IOC.IOC LPEInstance
parResetLoop lpeInstance successorsPerSummand = do
    newSuccessorsPerSummand <- parResetUpdate successorsPerSummand
    if newSuccessorsPerSummand == successorsPerSummand
    then do return lpeInstance -- TODO do something with the instance!!
    else parResetLoop lpeInstance newSuccessorsPerSummand
-- parResetLoop

parResetUpdate :: [(LPESummand, [LPESummand], [VarId])] -> IOC.IOC [(LPESummand, [LPESummand], [VarId])]
parResetUpdate successorsPerSummand = do return $ map checkSummand successorsPerSummand
  where
    checkSummand :: (LPESummand, [LPESummand], [VarId]) -> (LPESummand, [LPESummand], [VarId])
    checkSummand (summand@(LPESummand channelOffers guard _paramEqs), successors, unusedVars) =
        let channelOfferVars = foldl (++) [] (map snd channelOffers) in
        let guardVars = FreeVar.freeVars guard in
        let locallyUnusedVars = unusedVars List.\\ (guardVars List.\\ channelOfferVars) in
        let successorUnusedVars = [Set.fromList (uvars List.\\ (getSummandVarUsage smd uvars)) | (smd, _sucs, uvars) <- successorsPerSummand, suc <- successors, smd == suc ] in
        let newUnusedVars = foldl Set.intersection (Set.fromList locallyUnusedVars) successorUnusedVars in
          (summand, successors, Set.toList newUnusedVars)
    checkSummand other = other
    
    getSummandVarUsage (LPESummand _channelOffers _guard paramEqs) unusedVars =
        foldl (++) [] [FreeVar.freeVars v | (p, v) <- paramEqs, not (p `elem` unusedVars)]
    getSummandVarUsage _ _ = []
-- parResetUpdate

