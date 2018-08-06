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
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified FreeVar
import qualified Subst
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
    addSummandIfImmediateSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfImmediateSuccessor soFar summand@(LPESummand _ g _) = do
      sat <- isSatisfiable (Subst.subst (Map.fromList paramEqs) Map.empty g)
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
        case [ usedVars | (smd, _sucs, usedVars) <- successorsPerSummand, smd == summand ] of
          [usedVars] -> LPESummand channelOffers guard (updateParamEqs paramEqs usedVars)
          _ -> LPESummand channelOffers guard paramEqs
    updateSummand other = other
    
    updateParamEqs :: LPEParamEqs -> [VarId] -> LPEParamEqs
    updateParamEqs paramEqs usedVars = [ (p, if p `elem` usedVars then v else cstrConst (Cany { sort = varsort p })) | (p, v) <- paramEqs ]
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
    updateSummand (summand, successors, _usedVars) =
        let relevantToSuccessorVars = foldl Set.union Set.empty (map getRelevantToSuccessorVars successors) in
          (summand, successors, Set.toList relevantToSuccessorVars)
    
    getRelevantToSuccessorVars :: LPESummand -> Set.Set VarId
    getRelevantToSuccessorVars successor@(LPESummand channelOffers guard paramEqs) =
        let params = Set.fromList (map fst paramEqs) in
        let usedVars = foldl (++) [] [uvars | (s, _g, uvars) <- successorsPerSummand, s == successor] in
        
        -- Parameters in the guard are relevant to the successor, because they enable/disable the instantiation:
        let guardVars = Set.intersection params (Set.fromList (FreeVar.freeVars guard)) in
        
        -- Parameters used in assignments to used variables are relevant (because the variables are used):
        let assignmentVars = Set.intersection params (Set.fromList (foldl (++) [] [FreeVar.freeVars v | (p, v) <- paramEqs, q <- usedVars, p == q])) in
        
        -- The successor communicates via these variables, so their values are NOT relevant to the successor:
        let channelOfferVars = Set.intersection params (Set.fromList (foldl (++) [] (map snd channelOffers))) in
        
        -- Combine them all:
          (Set.union guardVars assignmentVars) Set.\\ channelOfferVars
    getRelevantToSuccessorVars _ = Set.empty
-- parResetUpdate

