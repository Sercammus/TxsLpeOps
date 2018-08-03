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
import           ConstDefs

-- LPE rewrite method.
-- Eliminates parameters that do not contribute to the behavior of a process from an LPE.
-- State spaces before and after are strongly bisimilar.
parReset :: LPEOperation
parReset lpeInstance@((_channels, paramEqs, summands)) = do
    immediateSuccessors <- Monad.mapM (getImmediateSuccessors summands) summands
    let successorsPerSummand = zipWith (\s i -> (s, i, map fst paramEqs)) summands immediateSuccessors
    newLPEInstance <- parResetLoop lpeInstance successorsPerSummand
    return (Just newLPEInstance)
-- parReset

-- Selects all potential successors summands of a given summand from a list with all summands:
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

-- Updates the information collected about summands, in particular their lists of unused variables,
-- until the information no longer changes.
-- With the final information, assign ANY values to variables that are unused:
parResetLoop :: LPEInstance -> [(LPESummand, [LPESummand], [VarId])] -> IOC.IOC LPEInstance
parResetLoop lpeInstance@(channels, initParamEqs, summands) successorsPerSummand = do
    if newSuccessorsPerSummand == successorsPerSummand
    then do return (channels, initParamEqs, map updateSummand summands)
    else parResetLoop lpeInstance newSuccessorsPerSummand
  where
    newSuccessorsPerSummand = parResetUpdate successorsPerSummand
    
    updateSummand :: LPESummand -> LPESummand
    updateSummand summand@(LPESummand channelOffers guard paramEqs) =
        case [ uvars | (smd, _sucs, uvars) <- successorsPerSummand, smd == summand ] of
          [uvars] -> LPESummand channelOffers guard (updateParamEqs paramEqs uvars)
          _ -> LPESummand channelOffers guard paramEqs
    updateSummand other = other
    
    updateParamEqs :: LPEParamEqs -> [VarId] -> LPEParamEqs
    updateParamEqs paramEqs unusedVars = [ (p, if p `elem` unusedVars then cstrConst (Cany { sort = varsort p }) else v) | (p, v) <- paramEqs ]
-- parResetLoop

-- Updates the information collected about summands, in particular their lists of unused variables:
parResetUpdate :: [(LPESummand, [LPESummand], [VarId])] -> [(LPESummand, [LPESummand], [VarId])]
parResetUpdate successorsPerSummand = map updateSummand successorsPerSummand
  where
    -- Initially, all variables are added to the list of unused variables of a summand.
    -- They are removed only if:
    --  * They occur in the condition of the summand while not being defined as a communication variable, e.g. "CHANNEL ? x"; or
    --  * They are used in the assignment to a variable that IS used by a potential successor summand.
    updateSummand :: (LPESummand, [LPESummand], [VarId]) -> (LPESummand, [LPESummand], [VarId])
    updateSummand (summand@(LPESummand channelOffers guard _paramEqs), successors, unusedVars) =
        let channelOfferVars = foldl (++) [] (map snd channelOffers) in
        let guardVars = FreeVar.freeVars guard in
        let locallyUnusedVars = unusedVars List.\\ (guardVars List.\\ channelOfferVars) in
        let successorUnusedVars = [ Set.fromList (uvars List.\\ (getSummandVarUsage smd uvars)) | (smd, _sucs, uvars) <- successorsPerSummand, suc <- successors, smd == suc ] in
        let newUnusedVars = foldl Set.intersection (Set.fromList locallyUnusedVars) successorUnusedVars in
          (summand, successors, Set.toList newUnusedVars)
    updateSummand other = other
    
    -- Of a given summand, determine which variables are used in its recursive call.
    -- Assignments to variables that are considered unused (for now) are ignored!
    getSummandVarUsage (LPESummand _channelOffers _guard paramEqs) unusedVars =
        foldl (++) [] [ FreeVar.freeVars v | (p, v) <- paramEqs, not (p `elem` unusedVars) ]
    getSummandVarUsage _ _ = []
-- parResetUpdate

