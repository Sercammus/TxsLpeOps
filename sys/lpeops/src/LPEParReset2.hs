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
import           VarFactory
import Constant hiding (sort)

parReset2 :: LPEOperation
parReset2 lpeInstance@((_channels, paramEqs, summands)) invariant = do
    let params = map fst paramEqs
    paramUsagePerSummand <- getParamUsagePerSummand summands params invariant
    -- rulingParamsPerSummand <- getRulingParamsPerSummand summands params invariant
    -- changingParamsPerSummand <- getChangingParamsPerSummand summands params invariant
    -- controlFlowParams <- getControlFlowParams summands rulingParamsPerSummand changingParamsPerSummand params invariant
    -- let controlFlowGraphs = Map.restrictKeys (getControlFlowGraphs (Map.toList rulingParamsPerSummand)) (Set.fromList controlFlowParams)
    -- let dataParams = params List.\\ controlFlowParams
    -- let belongsToRelation = getBelongsToRelation summands rulingParamsPerSummand changingParamsPerSummand controlFlowParams dataParams
    
    return (Just lpeInstance)
-- parReset2

-- Determines which of the specified data parameters belong to which of the specified control flow parameters.
-- A data parameter belongs to a control flow parameter if the data parameter is only changed in summands that are ruled by the control flow parameter.
getBelongsToRelation :: [LPESummand] -> (Map.Map LPESummand [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)]) -> (Map.Map LPESummand [VarId]) -> [VarId] -> [VarId] -> (Map.Map VarId [VarId])
getBelongsToRelation _summands _rulingParamsPerSummand _changingParamsPerSummand _controlFlowParams [] = Map.empty
getBelongsToRelation summands rulingParamsPerSummand changingParamsPerSummand controlFlowParams (d:ds) =
    let summandsWhereDChanges = Map.keys (Map.filter (\changingParams -> d `elem` changingParams) changingParamsPerSummand) in
    let foldRulingParams = \soFar smd -> Set.intersection soFar (Set.fromList (map (\(v, _, _) -> v) (Map.findWithDefault [] smd rulingParamsPerSummand))) in
    let paramsThatRuleD = Set.toList (foldl foldRulingParams (Set.fromList controlFlowParams) summandsWhereDChanges) in
    let ds' = getBelongsToRelation summands rulingParamsPerSummand changingParamsPerSummand controlFlowParams ds in
      Map.insert d paramsThatRuleD ds'
-- getBelongsToRelation

getControlFlowGraphs :: [(LPESummand, [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)])] -> (Map.Map VarId [(TxsDefs.VExpr, LPESummand, TxsDefs.VExpr)])
getControlFlowGraphs [] = Map.empty
getControlFlowGraphs ((summand, rulingParams):xs) =
    let newEntries = map (\(v, s1, s2) -> (v, [(s1, summand, s2)])) rulingParams in
      Map.unionWith (++) (Map.fromList newEntries) (getControlFlowGraphs xs)
-- getControlFlowGraphs

-- Determines which of the specified parameters are 'control flow parameters'; that is,
-- parameters that may only be changed by a summand if they 'rule' that summand (see getRulingParamsPerSummand).
-- This function requires information about which parameters are ruling the summands of the LPE; typically,
-- getRulingParamsPerSummand is used to obtain this information.
getControlFlowParams :: [LPESummand] -> (Map.Map LPESummand [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)]) -> (Map.Map LPESummand [VarId]) -> [VarId] -> TxsDefs.VExpr -> IOC.IOC [VarId]
getControlFlowParams _summands _rulingParamsPerSummand _changingParamsPerSummand [] _invariant = do return []
getControlFlowParams summands rulingParamsPerSummand changingParamsPerSummand (v:vs) invariant = do
    vs' <- getControlFlowParams summands rulingParamsPerSummand changingParamsPerSummand vs invariant
    if isRulingOrUnchangedInAllSummands summands
    then do return (v:vs')
    else do return vs'
  where
    isRulingOrUnchangedInAllSummands :: [LPESummand] -> Bool
    isRulingOrUnchangedInAllSummands [] = True
    isRulingOrUnchangedInAllSummands (x:xs) =
        let ruling = isRulingParam (Map.findWithDefault [] x rulingParamsPerSummand) in
        let unchanged = not (v `elem` (Map.findWithDefault [] x changingParamsPerSummand)) in
          (ruling || unchanged) && (isRulingOrUnchangedInAllSummands xs)
    -- isRulingOrUnchangedInAllSummands
    
    isRulingParam :: [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)] -> Bool
    isRulingParam [] = False
    isRulingParam ((varId, _, _):xs) = if varId == v then True else isRulingParam xs
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


