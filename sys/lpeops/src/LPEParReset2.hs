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

module LPEParReset2 (
parReset2
) where

import qualified Control.Monad       as Monad
import qualified Data.List           as List
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified FreeVar
import qualified TxsDefs
import qualified EnvData
import           LPEOps
import           LPEParUsage
import           Satisfiability
import           ValExprPrettyPrint
import           VarId
import           ValExpr

parReset2 :: LPEOperation
parReset2 lpeInstance@((_channels, paramEqs, summands)) invariant = do
    let params = map fst paramEqs
    paramUsagePerSummand <- getParamUsagePerSummand summands params invariant
    let controlFlowParams = getControlFlowParams summands paramUsagePerSummand params
    let dataParams = params List.\\ controlFlowParams
    let controlFlowGraphs = Map.restrictKeys (getControlFlowGraphs summands paramUsagePerSummand) (Set.fromList controlFlowParams)
    let belongsToRelation = getBelongsToRelation summands paramUsagePerSummand controlFlowParams dataParams
    let initialRelevanceRelation = concat [
                                     concat [
                                       [ (dk, dj, s) | (dj', s) <- Map.toList (paramSources paramUsage), dj' == dj ]
                                     | dj <- djs, paramUsage <- Map.elems paramUsagePerSummand, dk `elem` (directlyUsedParams paramUsage) ]
                                   | (dk, djs) <- Map.toList belongsToRelation ]
    let relevanceRelation = repeatUntilFixpoint (updateRelevanceRelation paramUsagePerSummand controlFlowGraphs belongsToRelation) (Set.fromList initialRelevanceRelation)
      
    return (Just lpeInstance)
-- parReset2

repeatUntilFixpoint :: Eq t => (t -> t) -> t -> t
repeatUntilFixpoint f i = let i' = f i in if i == i' then i else repeatUntilFixpoint f i'

updateRelevanceRelation :: Map.Map LPESummand LPEParamUsage                             -- paramUsagePerSummand
                        -> Map.Map VarId [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)]   -- controlFlowGraphs
                        -> Map.Map VarId [VarId]                                        -- belongsToRelation
                        -> Set.Set (VarId, VarId, TxsDefs.VExpr)                        -- relevanceRelationSoFar
                        -> Set.Set (VarId, VarId, TxsDefs.VExpr)                        -- newRelevanceRelation
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
                          [ (dk, dj, s) | (dj', s) <- Map.toList (paramSources (extractParamUsage i paramUsagePerSummand)), dj' == dj ]
                        | (_r, i, t') <- Map.findWithDefault [] dp controlFlowGraphs, t' == t, dk `elem` (extractParamEqVars i dl) ]
                      | (dl', dp, t) <- update1, dl' == dl ]
                    | dj <- dkjs, not (dj `elem` dljs) ]
                  | (dk, dkjs) <- Map.toList belongsToRelation, (dl, dljs) <- Map.toList belongsToRelation ] in
      Set.union relevanceRelationSoFar (Set.fromList update2)
-- updateRelevanceRelation

extractParamEqVars :: LPESummand -> VarId -> [VarId]
extractParamEqVars (LPESummand _channelOffers _guard LPEStop) _varId = []
extractParamEqVars (LPESummand _channelOffers _guard (LPEProcInst paramEqs)) varId =
    let assignmentVars = concat [ FreeVar.freeVars v | (p, v) <- paramEqs, p == varId ] in
      List.intersect assignmentVars (map fst paramEqs)
-- extractParamEqVars

-- Determines which of the specified data parameters belong to which of the specified control flow parameters.
-- A data parameter belongs to a control flow parameter if the data parameter is only changed in summands that are ruled by the control flow parameter.
getBelongsToRelation :: [LPESummand] -> Map.Map LPESummand LPEParamUsage -> [VarId] -> [VarId] -> Map.Map VarId [VarId]
getBelongsToRelation _summands _paramUsagePerSummand _controlFlowParams [] = Map.empty
getBelongsToRelation summands paramUsagePerSummand controlFlowParams (d:ds) =
    let summandsWhereDChanges = Map.keys (Map.filter (\paramUsage -> d `elem` (changedParams paramUsage)) paramUsagePerSummand) in
    let foldRulingParams = \soFar smd -> Set.intersection soFar (Set.fromList (rulingParams (extractParamUsage smd paramUsagePerSummand))) in
    let paramsThatRuleD = Set.toList (foldl foldRulingParams (Set.fromList controlFlowParams) summandsWhereDChanges) in
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
        let paramSource = extractParamSource rulingPar (paramSources paramUsage) in
        let paramDestination = extractParamDestination rulingPar (paramDestinations paramUsage) in
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

resetParamsInSummand :: LPEInstance -> [(LPESummand, [LPESummand], [VarId])] -> LPESummand -> IOC.IOC LPESummand
resetParamsInSummand _ _ (summand@(LPESummand _ _ LPEStop)) = do return summand
resetParamsInSummand (_, initParamEqs, summands) successorsPerSummand summand@(LPESummand channelOffers guard (LPEProcInst paramEqs)) =
    case [ (sucs, uvars) | (smd, sucs, uvars) <- successorsPerSummand, smd == summand ] of
      [(sucs, uvars)] -> if (length uvars) == (length initParamEqs)
                         then do return summand
                         else do let substConstraint = cstrAnd (Set.fromList (guard:(map (\(LPESummand _ g _) -> cstrNot (varSubst paramEqs g)) [smd | smd <- summands, not (smd `elem` sucs)])))
                                 sol <- getSomeSolution substConstraint (map fst initParamEqs)
                                 case sol of
                                   Just solMap -> do let newParamEqs = [ (p, if p `elem` uvars then v else (Map.findWithDefault v p solMap)) | (p, v) <- paramEqs ]
                                                     let zippedEqs = filter (\(eq1, _) -> not ((fst eq1) `elem` uvars)) (zip paramEqs newParamEqs)
                                                     let Just summandNumber = (List.elemIndex summand summands)
                                                     Monad.mapM_ (\((p, v), (_, w)) -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("\t" ++ (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr w) ++ " instead of " ++ (showValExpr v) ++ " in " ++ (numberToString (summandNumber + 1)) ++ " summand") ]) zippedEqs
                                                     return (LPESummand channelOffers guard (LPEProcInst newParamEqs))
                                   Nothing -> do return summand
      _ -> do return summand
  where
    numberToString :: Int -> String
    numberToString number =
        (show number) ++
        (case number `mod` 10 of
          1 -> "st"
          2 -> "nd"
          3 -> "rd"
          _ -> "th")
-- resetParamsInSummand


