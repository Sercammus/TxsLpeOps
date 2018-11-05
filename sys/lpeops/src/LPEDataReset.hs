{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEDataReset
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEDataReset (
dataReset
) where

import qualified Control.Monad as Monad
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified FreeVar
import qualified TxsDefs
import qualified EnvCore as IOC
import qualified EnvData
import LPEOps
import LPEParUsage
import VarId
import LPEPrettyPrint

dataReset :: LPEOperation
dataReset (channels, initParamEqs, summands) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<dataReset>>" ]
    let params = Map.keys initParamEqs
    paramUsagePerSummand <- getParamUsagePerSummand (Set.toList summands) params invariant
    let controlFlowParams = getControlFlowParams (Set.toList summands) paramUsagePerSummand params
    let dataParams = params List.\\ controlFlowParams
    let controlFlowGraphs = Map.restrictKeys (getControlFlowGraphs (Set.toList summands) paramUsagePerSummand) (Set.fromList controlFlowParams)
    let belongsToRelation = getBelongsToRelation (Set.toList summands) paramUsagePerSummand controlFlowParams dataParams
    let initialRelevanceRelation = concat [
                                     concat [
                                       [ (dk, dj, s) | (dj', s) <- Map.toList (paramSources paramUsage), dj' == dj ]
                                     | dj <- djs, paramUsage <- Map.elems paramUsagePerSummand, dk `elem` (directlyUsedParams paramUsage) ]
                                   | (dk, djs) <- Map.toList belongsToRelation ]
    let relevanceRelation = repeatUntilFixpoint (updateRelevanceRelation paramUsagePerSummand controlFlowGraphs belongsToRelation) (Set.fromList initialRelevanceRelation)
    let newSummands = map (resetParamsInSummand initParamEqs paramUsagePerSummand belongsToRelation relevanceRelation) (Set.toList summands)
    Monad.mapM_ (\m -> IOC.putMsgs [ EnvData.TXS_CORE_ANY m ]) (concat (map snd newSummands))
    return (Right (channels, initParamEqs, Set.fromList (map fst newSummands)))
-- dataReset

resetParamsInSummand :: Map.Map VarId TxsDefs.VExpr             -- initParamEqs
                     -> Map.Map LPESummand LPEParamUsage        -- paramUsagePerSummand
                     -> Map.Map VarId [VarId]                   -- belongsToRelation
                     -> Set.Set (VarId, VarId, TxsDefs.VExpr)   -- relevanceRelation
                     -> LPESummand                              -- summand
                     -> (LPESummand, [String])                  -- result
resetParamsInSummand _initParamEqs _paramUsagePerSummand _belongsToRelation _relevanceRelation (summand@(LPESummand _ _ _ LPEStop)) = (summand, [])
resetParamsInSummand initParamEqs paramUsagePerSummand belongsToRelation relevanceRelation summand@(LPESummand channelVars channelOffers guard (LPEProcInst paramEqs)) =
    let paramUsage = extractParamUsage summand paramUsagePerSummand in
    let newParamEqs = map (resetParam paramUsage) (Map.toList paramEqs) in
      (LPESummand channelVars channelOffers guard (LPEProcInst (Map.fromList newParamEqs)), concat (map getParamChange newParamEqs))
  where
    resetParam :: LPEParamUsage -> (VarId, TxsDefs.VExpr) -> (VarId, TxsDefs.VExpr)
    resetParam paramUsage (p, v) =
        let requiredElements = Set.fromList (
                                 concat [
                                   [ (dk, dj, mapGet (paramDestinations paramUsage) dj) | dj <- djs, dj `elem` (rulingParams paramUsage) ]
                                 | (dk, djs) <- Map.toList belongsToRelation, dk == p ]
                               ) in
          if (Set.intersection relevanceRelation requiredElements) == requiredElements
          then (p, v)
          else (p, mapGet initParamEqs p)
    -- resetParam
    
    getParamChange :: (VarId, TxsDefs.VExpr) -> [String]
    getParamChange (p, v) =
        if (mapGet paramEqs p) /= v
        then ["Setting " ++ (Text.unpack (VarId.name p)) ++ " to " ++ (showValExpr v) ++ " instead of " ++ (showValExpr (mapGet paramEqs p))]
        else []
    -- getParamChange
-- resetParamsInSummand

repeatUntilFixpoint :: Eq t => (t -> t) -> t -> t
repeatUntilFixpoint f i = let i' = f i in if i == i' then i else repeatUntilFixpoint f i'

updateRelevanceRelation :: Map.Map LPESummand LPEParamUsage                             -- paramUsagePerSummand
                        -> Map.Map VarId [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)]   -- controlFlowGraphs
                        -> Map.Map VarId [VarId]                                        -- belongsToRelation
                        -> Set.Set (VarId, VarId, TxsDefs.VExpr)                        -- relevanceRelationSoFar
                        -> Set.Set (VarId, VarId, TxsDefs.VExpr)                        -- result
updateRelevanceRelation paramUsagePerSummand controlFlowGraphs belongsToRelation relevanceRelationSoFar =
    let update1 = concat [
                    concat [
                      concat [
                        [ (dk, dj, s) | (s, i, t') <- Map.findWithDefault [] dj controlFlowGraphs, t' == t, dk `elem` (extractParamEqVars i dl) ]
                        | (dl, dj', t) <- Set.toList relevanceRelationSoFar, dj' == dj ]
                      | dj <- djs ]
                    | (dk, djs) <- Map.toList belongsToRelation ] in
    let update2 = concat [
                    concat [
                      concat [
                        concat [
                          [ (dk, dj, s) | (dj', s) <- Map.toList (paramSources (mapGet paramUsagePerSummand i)), dj' == dj ]
                        | (_r, i, t') <- Map.findWithDefault [] dp controlFlowGraphs, t' == t, dk `elem` (extractParamEqVars i dl) ]
                      | (dl', dp, t) <- update1, dl' == dl ]
                    | dj <- dkjs, not (dj `elem` dljs) ]
                  | (dk, dkjs) <- Map.toList belongsToRelation, (dl, dljs) <- Map.toList belongsToRelation ] in
      Set.union relevanceRelationSoFar (Set.fromList update2)
-- updateRelevanceRelation

extractParamEqVars :: LPESummand -> VarId -> [VarId]
extractParamEqVars (LPESummand _ _ _ LPEStop) _varId = []
extractParamEqVars (LPESummand _ _ _ (LPEProcInst paramEqs)) varId =
    let assignmentVars = Set.fromList (FreeVar.freeVars (mapGet paramEqs varId)) in
      Set.toList (Set.intersection (Map.keysSet paramEqs) assignmentVars)
-- extractParamEqVars

-- Determines which of the specified data parameters belong to which of the specified control flow parameters.
-- A data parameter belongs to a control flow parameter if the data parameter is only changed in summands that are ruled by the control flow parameter.
getBelongsToRelation :: [LPESummand] -> Map.Map LPESummand LPEParamUsage -> [VarId] -> [VarId] -> Map.Map VarId [VarId]
getBelongsToRelation _summands _paramUsagePerSummand _controlFlowParams [] = Map.empty
getBelongsToRelation summands paramUsagePerSummand controlFlowParams (d:ds) =
    let summandsWhereDIsChangedOrUsed = Map.keys (Map.filter (\paramUsage -> (d `elem` (changedParams paramUsage)) || (d `elem` (changedParams paramUsage))) paramUsagePerSummand) in
    let foldRulingParams = \soFar smd -> Set.intersection soFar (Set.fromList (rulingParams (extractParamUsage smd paramUsagePerSummand))) in
    let paramsThatRuleD = Set.toList (foldl foldRulingParams (Set.fromList controlFlowParams) summandsWhereDIsChangedOrUsed) in
    let ds' = getBelongsToRelation summands paramUsagePerSummand controlFlowParams ds in
      Map.insert d paramsThatRuleD ds'
-- getBelongsToRelation

getControlFlowGraphs :: [LPESummand] -> Map.Map LPESummand LPEParamUsage -> Map.Map VarId [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)]
getControlFlowGraphs [] _paramUsagePerSummand = Map.empty
getControlFlowGraphs (x:xs) paramUsagePerSummand =
    let newEntries = map constructEdgeFromRulingPar (rulingParams paramUsage) in
      Map.unionWith (++) (Map.fromList newEntries) (getControlFlowGraphs xs paramUsagePerSummand)
  where
    paramUsage :: LPEParamUsage
    paramUsage = extractParamUsage x paramUsagePerSummand
    
    constructEdgeFromRulingPar :: VarId -> (VarId, [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)])
    constructEdgeFromRulingPar rulingPar =
        let paramSource = mapGet (paramSources paramUsage) rulingPar in
        let paramDestination = mapGet (paramDestinations paramUsage) rulingPar in
          (rulingPar, [(paramSource, x, paramDestination)])
-- getControlFlowGraphs

-- Determines which of the specified parameters are 'control flow parameters'; that is,
-- parameters that may only be changed by a summand if they 'rule' that summand (see getRulingParamsPerSummand).
-- This function requires information about which parameters are ruling the summands of the LPE; typically,
-- getRulingParamsPerSummand is used to obtain this information.
getControlFlowParams :: [LPESummand] -> Map.Map LPESummand LPEParamUsage -> [VarId] -> [VarId]
getControlFlowParams _summands _paramUsagePerSummand [] = []
getControlFlowParams summands paramUsagePerSummand params =
    filter (isRulingOrUnchangedInAllSummands summands) params
  where
    isRulingOrUnchangedInAllSummands :: [LPESummand] -> VarId -> Bool
    isRulingOrUnchangedInAllSummands [] _ = True
    isRulingOrUnchangedInAllSummands (x:xs) v =
        let paramUsage = extractParamUsage x paramUsagePerSummand in
        let ruling = v `elem` (rulingParams paramUsage) in
        let unchanged = not (v `elem` (changedParams paramUsage)) in
          (ruling || unchanged) && (isRulingOrUnchangedInAllSummands xs v)
-- getControlFlowParams

