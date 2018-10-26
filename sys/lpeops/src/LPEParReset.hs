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
import qualified Data.List           as List
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified FreeVar
import qualified EnvData
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           LPEPrettyPrint
import           VarId
import           ValExpr
import           LPESuccessors

-- LPE rewrite method.
-- Eliminates parameters that do not contribute to the behavior of a process from an LPE.
-- State spaces before and after are strongly bisimilar.
parReset :: LPEOperation
parReset lpeInstance@((_channels, paramEqs, summands)) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Identifying successors..." ]
    possibleSuccessors <- Monad.mapM (getPossibleSuccessors summands invariant) summands
    let successorsPerSummand = zipWith (\s i -> (s, i, Map.keys paramEqs)) summands possibleSuccessors
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Analyzing control flow..." ]
    newLPE <- parResetLoop lpeInstance invariant successorsPerSummand
    return (Right newLPE)
-- parReset

-- Updates the information collected about summands, in particular their lists of used variables,
-- until the information no longer changes.
-- With the final information, assign ANY values to variables that are unused:
parResetLoop :: LPEInstance -> TxsDefs.VExpr -> [(LPESummand, [LPESummand], [VarId])] -> IOC.IOC LPEInstance
parResetLoop lpeInstance@(channels, initParamEqs, summands) invariant successorsPerSummand = do
    let newSuccessorsPerSummand = parResetUpdate successorsPerSummand
    if newSuccessorsPerSummand == successorsPerSummand
    then do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Resetting the following parameters:" ]
            newSummands <- Monad.mapM (resetParamsInSummand lpeInstance invariant successorsPerSummand) summands
            return (channels, initParamEqs, newSummands)
    else parResetLoop lpeInstance invariant newSuccessorsPerSummand
-- parResetLoop

resetParamsInSummand :: LPEInstance -> TxsDefs.VExpr -> [(LPESummand, [LPESummand], [VarId])] -> LPESummand -> IOC.IOC LPESummand
resetParamsInSummand _ _ _ (summand@(LPESummand _ _ _ LPEStop)) = do return summand
resetParamsInSummand (_, initParamEqs, summands) invariant successorsPerSummand summand@(LPESummand channelVars channelOffers guard (LPEProcInst paramEqs)) =
    case [ (sucs, uvars) | (smd, sucs, uvars) <- successorsPerSummand, smd == summand ] of
      [(sucs, uvars)] -> if (length uvars) == (length initParamEqs)
                         then do return summand -- (All variables are used, apparently, so do not touch the summand.)
                         else do let nonSuccessors = Set.toList ((Set.fromList summands) Set.\\ (Set.fromList sucs))
                                 let newParamEqs = Map.union (Map.filterWithKey (\p _ -> p `elem` uvars) paramEqs) (Map.filterWithKey (\p _ -> not (p `elem` uvars)) initParamEqs)
                                 constraints <- Monad.mapM (summandToConstraint newParamEqs) nonSuccessors
                                 notSat <- areNotSatisfiable constraints invariant
                                 if notSat
                                 then do printNewParamEqs newParamEqs
                                         return (LPESummand channelVars channelOffers guard (LPEProcInst newParamEqs))
                                 else do return summand
      _ -> do return summand
  where
    printNewParamEqs :: LPEParamEqs -> IOC.IOC ()
    printNewParamEqs newParamEqs = do
        let changedParamEqs = Map.filterWithKey (\p v -> v /= (paramEqs Map.! p)) newParamEqs
        let Just summandNumber = (List.elemIndex summand summands)
        Monad.mapM_ (\((p, v)) -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("\t" ++ (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr v) ++ " instead of " ++ (showValExpr (paramEqs Map.! p)) ++ " in " ++ (numberToString (summandNumber + 1)) ++ " summand") ]) (Map.toList changedParamEqs)
    -- printNewParamEqs
    
    summandToConstraint :: LPEParamEqs -> LPESummand -> IOC.IOC TxsDefs.VExpr
    summandToConstraint newParamEqs (LPESummand _ _ g _) = do
        g' <- doBlindSubst newParamEqs g
        return (cstrAnd (Set.fromList [guard, g']))
    -- summandToConstraint
    
    numberToString :: Int -> String
    numberToString number =
        (show number) ++
        (case number `mod` 10 of
          1 -> "st"
          2 -> "nd"
          3 -> "rd"
          _ -> "th")
    -- numberToString
-- resetParamsInSummand

-- Updates the information collected about summands, in particular their lists of used variables:
parResetUpdate :: [(LPESummand, [LPESummand], [VarId])] -> [(LPESummand, [LPESummand], [VarId])]
parResetUpdate successorsPerSummand = map updateSummand successorsPerSummand
  where
    -- Initially, all variables are added to the list of used variables of a summand.
    -- They are removed only if:
    --  * They occur in the condition of the summand while not being defined as a communication variable, e.g. "CHANNEL ? x"; or
    --  * They are used in the assignment to a variable that IS used by a potential successor summand.
    updateSummand :: (LPESummand, [LPESummand], [VarId]) -> (LPESummand, [LPESummand], [VarId])
    updateSummand (summand, successors, _usedVars) =
        let relevantToSuccessorVars = foldl Set.union Set.empty (map getRelevantToSuccessorVars successors) in
          (summand, successors, Set.toList relevantToSuccessorVars)
    
    getRelevantToSuccessorVars :: LPESummand -> Set.Set VarId
    getRelevantToSuccessorVars successor@(LPESummand _channelVars channelOffers guard procInst) =
        let usedVars = concat [uvars | (s, _g, uvars) <- successorsPerSummand, s == successor] in
        
        -- Parameters in the guard are relevant to the successor, because they enable/disable the channel+instantiation:
        let guardVars = Set.fromList (FreeVar.freeVars guard) in
        
        -- Parameters used in assignments to used variables are relevant (because the variables are used):
        let assignmentVars = (case procInst of
                                LPEProcInst paramEqs -> Set.fromList (concat [FreeVar.freeVars (paramEqs Map.! u) | u <- usedVars])
                                _ -> Set.empty) in
        
        -- The successor communicates via these variables, so their values are NOT relevant to the successor:
        let channelOfferVars = Set.fromList (concat (map snd channelOffers)) in
        
        -- Combine them all:
          (Set.union guardVars assignmentVars) Set.\\ channelOfferVars
-- parResetUpdate

