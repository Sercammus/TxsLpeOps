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

mapGet :: (Show a, Ord a) => Map.Map a b -> a -> b
mapGet m k =
    --trace ("mapGet(" ++ (show k) ++ ")") (
      if Map.member k m
      then m Map.! k
      else error ("Could not find " ++ show k ++ " in map!")
    --)
-- mapGet

repeatUntilFixpoint :: Eq t => (t -> t) -> t -> t
repeatUntilFixpoint f i = let i' = f i in if i == i' then i else repeatUntilFixpoint f i'

dataReset :: LPEOperation
dataReset (channels, initParamEqs, summands) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<dataReset>>" ]
    let params = Map.keysSet initParamEqs
    paramUsagePerSummand <- getParamUsagePerSummand summands params invariant
    -- IOC.putMsgs [ EnvData.TXS_CORE_ANY (showLPEParamUsagePerSummand paramUsagePerSummand) ]
    let controlFlowParams = getControlFlowParams paramUsagePerSummand params
    let dataParams = params Set.\\ controlFlowParams
    let controlFlowGraphs = getControlFlowGraphs paramUsagePerSummand controlFlowParams
    let belongsToRelation = getBelongsToRelation paramUsagePerSummand controlFlowParams dataParams
    let initialRelevanceRelation = concat [
                                     concat [
                                       [ (dk, dj, s) | (dj', s) <- Map.toList (paramSources paramUsage), dj' == dj ]
                                     | dj <- djs, paramUsage <- Map.elems paramUsagePerSummand, dk `elem` directlyUsedParams paramUsage ]
                                   | (dk, djs) <- Map.toList belongsToRelation ]
    let relevanceRelation = repeatUntilFixpoint (updateRelevanceRelation paramUsagePerSummand controlFlowGraphs belongsToRelation) (Set.fromList initialRelevanceRelation)
    let newSummands = map (resetParamsInSummand initParamEqs paramUsagePerSummand belongsToRelation relevanceRelation) (Set.toList summands)
    Monad.mapM_ (\m -> IOC.putMsgs [ EnvData.TXS_CORE_ANY m ]) (concatMap snd newSummands)
    return (Right (channels, initParamEqs, Set.fromList (map fst newSummands)))
-- dataReset

resetParamsInSummand :: Map.Map VarId TxsDefs.VExpr             -- initParamEqs
                     -> Map.Map LPESummand LPEParamUsage        -- paramUsagePerSummand
                     -> Map.Map VarId [VarId]                   -- belongsToRelation
                     -> Set.Set (VarId, VarId, TxsDefs.VExpr)   -- relevanceRelation
                     -> LPESummand                              -- summand
                     -> (LPESummand, [String])                  -- result
resetParamsInSummand _initParamEqs _paramUsagePerSummand _belongsToRelation _relevanceRelation summand@(LPESummand _ _ _ LPEStop) = (summand, [])
resetParamsInSummand initParamEqs paramUsagePerSummand belongsToRelation relevanceRelation summand@(LPESummand channelVars channelOffers guard (LPEProcInst paramEqs)) =
    let paramUsage = paramUsagePerSummand Map.! summand in
    let newParamEqs = map (resetParam paramUsage) (Map.toList paramEqs) in
      (LPESummand channelVars channelOffers guard (LPEProcInst (Map.fromList newParamEqs)), concatMap getParamChange newParamEqs)
  where
    resetParam :: LPEParamUsage -> (VarId, TxsDefs.VExpr) -> (VarId, TxsDefs.VExpr)
    resetParam paramUsage (p, v) =
        let requiredElements = Set.fromList (
                                 concat [
                                   [ (dk, dj, mapGet (paramDestinations paramUsage) dj) | dj <- djs, dj `elem` rulingParams paramUsage ]
                                 | (dk, djs) <- Map.toList belongsToRelation, dk == p ]
                               ) in
          if Set.intersection relevanceRelation requiredElements == requiredElements
          then (p, v)
          else (p, mapGet initParamEqs p)
    -- resetParam
    
    getParamChange :: (VarId, TxsDefs.VExpr) -> [String]
    getParamChange (p, v) = ["Setting " ++ Text.unpack (VarId.name p) ++ " to " ++ showValExpr v ++ " instead of " ++ showValExpr (mapGet paramEqs p) | mapGet paramEqs p /= v]
    -- getParamChange
-- resetParamsInSummand

updateRelevanceRelation :: Map.Map LPESummand LPEParamUsage                             -- paramUsagePerSummand
                        -> Map.Map VarId [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)]   -- controlFlowGraphs
                        -> Map.Map VarId [VarId]                                        -- belongsToRelation
                        -> Set.Set (VarId, VarId, TxsDefs.VExpr)                        -- relevanceRelationSoFar
                        -> Set.Set (VarId, VarId, TxsDefs.VExpr)                        -- result
updateRelevanceRelation paramUsagePerSummand controlFlowGraphs belongsToRelation relevanceRelationSoFar =
    let update1 = concat [
                    concat [
                      concat [
                        [ (dk, dj, s) | (s, i, t') <- Map.findWithDefault [] dj controlFlowGraphs, t' == t, dk `elem` extractParamEqVars i dl ]
                        | (dl, dj', t) <- Set.toList relevanceRelationSoFar, dj' == dj ]
                      | dj <- djs ]
                    | (dk, djs) <- Map.toList belongsToRelation ] in
    let update2 = concat [
                    concat [
                      concat [
                        concat [
                          [ (dk, dj, s) | (dj', s) <- Map.toList (paramSources (mapGet paramUsagePerSummand i)), dj' == dj ]
                        | (_r, i, t') <- Map.findWithDefault [] dp controlFlowGraphs, t' == t, dk `elem` extractParamEqVars i dl ]
                      | (dl', dp, t) <- update1, dl' == dl ]
                    | dj <- dkjs, dj `notElem` dljs ]
                  | (dk, dkjs) <- Map.toList belongsToRelation, (dl, dljs) <- Map.toList belongsToRelation ] in
      Set.union relevanceRelationSoFar (Set.fromList update2)
-- updateRelevanceRelation

extractParamEqVars :: LPESummand -> VarId -> [VarId]
extractParamEqVars (LPESummand _ _ _ LPEStop) _varId = []
extractParamEqVars (LPESummand _ _ _ (LPEProcInst paramEqs)) varId =
    let assignmentVars = Set.fromList (FreeVar.freeVars (mapGet paramEqs varId)) in
      Set.toList (Set.intersection (Map.keysSet paramEqs) assignmentVars)
-- extractParamEqVars

-- Determines which of the specified data parameters belong to which (set of) specified control flow parameters.
-- A data parameter belongs to a control flow parameter if the data parameter is only changed or used in summands that are ruled by the control flow parameter.
getBelongsToRelation :: Map.Map LPESummand LPEParamUsage -> Set.Set VarId -> Set.Set VarId -> Map.Map VarId [VarId]
getBelongsToRelation paramUsagePerSummand controlFlowParams dataParams
    | dataParams == Set.empty = Map.empty
    | otherwise =
        let whereDataParamsAreChangedOrUsed = Map.fromSet getWhereDataParamIsChangedOrUsed dataParams in
          Map.map (Set.toList . getCfpsToWhichDataParamsBelong) whereDataParamsAreChangedOrUsed
  where
    getWhereDataParamIsChangedOrUsed :: VarId -> Map.Map LPESummand LPEParamUsage
    getWhereDataParamIsChangedOrUsed param = Map.filter (\paramUsage -> (param `elem` changedParams paramUsage) || (param `elem` changedParams paramUsage)) paramUsagePerSummand
    
    getCfpsToWhichDataParamsBelong :: Map.Map LPESummand LPEParamUsage -> Set.Set VarId
    getCfpsToWhichDataParamsBelong whereDataParamIsChangedOrUsed =
        let rulingParamsWhereDataParamIsChangedOrUsed = map rulingParams (Map.elems whereDataParamIsChangedOrUsed) in
          foldl Set.intersection controlFlowParams rulingParamsWhereDataParamIsChangedOrUsed
    -- getCfpsToWhichDataParamsBelong
-- getBelongsToRelation

getControlFlowGraphs :: Map.Map LPESummand LPEParamUsage -> Set.Set VarId -> Map.Map VarId [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)]
getControlFlowGraphs paramUsagePerSummand = Map.fromSet (Set.toList . getControlFlowGraph)
  where
    getControlFlowGraph :: VarId -> Set.Set (TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)
    getControlFlowGraph controlFlowParam = Set.unions (map (getControlFlowGraphEdges controlFlowParam) (Map.toList paramUsagePerSummand))
    
    getControlFlowGraphEdges :: VarId -> (LPESummand, LPEParamUsage) -> Set.Set (TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)
    getControlFlowGraphEdges controlFlowParam (summand, paramUsage) =
        if controlFlowParam `elem` rulingParams paramUsage
        then let paramSource = paramSources paramUsage Map.! controlFlowParam in
             let paramDestination = paramDestinations paramUsage Map.! controlFlowParam in
               Set.singleton (paramSource, summand, paramDestination)
        else Set.empty
-- getControlFlowGraphs

-- Determines which of the specified parameters are 'control flow parameters'; that is,
-- parameters that may only be changed by a summand if they 'rule' that summand (see getRulingParamsPerSummand).
-- This function requires information about which parameters are ruling the summands of the LPE; typically,
-- getRulingParamsPerSummand is used to obtain this information.
getControlFlowParams :: Map.Map LPESummand LPEParamUsage -> Set.Set VarId -> Set.Set VarId
getControlFlowParams paramUsagePerSummand = Set.filter isControlFlowParam
  where
    isControlFlowParam :: VarId -> Bool
    isControlFlowParam param = Map.filter (isUnchangedOrRulingParam param) paramUsagePerSummand == paramUsagePerSummand
    
    isUnchangedOrRulingParam :: VarId -> LPEParamUsage -> Bool
    isUnchangedOrRulingParam param paramUsage =
        let unchanged = param `notElem` changedParams paramUsage in
        let ruling = param `elem` rulingParams paramUsage in
          unchanged || ruling
-- getControlFlowParams

