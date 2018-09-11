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
import           Satisfiability
import           ValExprPrettyPrint
import           VarId
import           ValExpr
import           VarFactory
import Constant hiding (sort)

parReset2 :: LPEOperation
parReset2 lpeInstance@((_channels, paramEqs, summands)) invariant = do
    let params = map fst paramEqs
    rulingParamsPerSummand <- getRulingParamsPerSummand summands params invariant
    controlFlowParams <- getControlFlowParams rulingParamsPerSummand params invariant
    let _belongsToRelation = getBelongsToRelation rulingParamsPerSummand controlFlowParams (params List.\\ controlFlowParams)
    return (Just lpeInstance)
-- parReset2

-- Determines which of the specified DATA parameters belong to which of the specified CONTROL FLOW parameters:
getBelongsToRelation :: [(LPESummand, [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)])] -> [VarId] -> [VarId] -> [(VarId, [VarId])]
getBelongsToRelation rulingParamsPerSummand controlFlowParams dataParams = getBelongsToVars dataParams
  where
    getBelongsToVars :: [VarId] -> [(VarId, [VarId])]
    getBelongsToVars (v:vs) = []
        -- let furtherBelongsToVars = getBelongsToVars vs in
        
-- getBelongsToRelation

-- Determines which of the specified parameters are 'control flow parameters'; that is,
-- parameters that only change in a summand if they rule that summand (see getRulingParamsPerSummand).
-- This function requires information about which parameters are ruling the summands of the LPE; typically,
-- getRulingParamsPerSummand is used to obtain this information.
getControlFlowParams :: [(LPESummand, [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)])] -> [VarId] -> TxsDefs.VExpr -> IOC.IOC [VarId]
getControlFlowParams _rulingParamsPerSummand [] _invariant = do return []
getControlFlowParams rulingParamsPerSummand (v:vs) invariant = do
    vs' <- getControlFlowParams rulingParamsPerSummand vs invariant
    ruling <- isRulingOrUnchangedInAllSummands rulingParamsPerSummand
    return (if ruling then (v:vs') else vs')
  where
    isRulingOrUnchangedInAllSummands :: [(LPESummand, [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)])] -> IOC.IOC Bool
    isRulingOrUnchangedInAllSummands [] = do return True
    isRulingOrUnchangedInAllSummands ((summand, rulingParams):xs) = do
        if isRulingParam rulingParams
        then do isRulingOrUnchangedInAllSummands xs
        else do (_, destSatExpr) <- constructDestSatExpr summand v invariant
                isTautology destSatExpr
    -- isRulingOrUnchangedInAllSummands
    
    isRulingParam :: [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)] -> Bool
    isRulingParam [] = False
    isRulingParam ((varId, _, _):xs) = if varId == v then True else isRulingParam xs
-- getControlFlowParams

-- Determines the parameters that 'rule' a summand for all specified summands.
-- A 'ruling' parameter is a parameter that has a unique value before and after the summand whenever the summand is enabled.
getRulingParamsPerSummand :: [LPESummand] -> [VarId] -> TxsDefs.VExpr -> IOC.IOC [(LPESummand, [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)])]
getRulingParamsPerSummand [] _ _ = do return []
getRulingParamsPerSummand (x:xs) params invariant = do
    rulingParams <- getRulingParams x params
    xs' <- getRulingParamsPerSummand xs params invariant
    return ((x, rulingParams):xs')
  where
    getRulingParams :: LPESummand -> [VarId] -> IOC.IOC [(VarId, TxsDefs.VExpr, TxsDefs.VExpr)]
    getRulingParams _ [] = do return []
    getRulingParams (LPESummand _ _ LPEStop) _ = do return []
    getRulingParams summand@(LPESummand _channelOffers guard (LPEProcInst _)) (p:ps) = do
        furtherRulingParams <- getRulingParams summand ps
        -- p rules the summand if p is assigned a unique value regardless of how the guard is solved:
        sourceSolution <- getUniqueSolution (cstrAnd (Set.fromList [guard, invariant])) [] [p]
        case sourceSolution of
          Just srcSolMap -> do -- Same for when solving the 'destVarExpr':
                               (destVar, destSatExpr) <- constructDestSatExpr summand p invariant
                               targetSolution <- getUniqueSolution destSatExpr [] [destVar]
                               case targetSolution of
                                 Just tgtSolMap -> do return ((p, extractValueFromSolution p srcSolMap, extractValueFromSolution destVar tgtSolMap):furtherRulingParams)
                                 _ -> return furtherRulingParams
          _ -> return furtherRulingParams
-- getRulingParamsPerSummand

-- Constructs an expression that we want to SAT-solve, and also gives the variable that
-- should always be assigned a unique value, regardless of how the expression is solved.
-- (This is because the 'destination' of a variable should be unique for each summand.)
constructDestSatExpr :: LPESummand -> VarId -> TxsDefs.VExpr -> IOC.IOC (VarId, TxsDefs.VExpr)
constructDestSatExpr (LPESummand _ _ LPEStop) varId _invariant = do return (varId, cstrConst (Cbool False))
constructDestSatExpr (LPESummand _channelOffers guard (LPEProcInst paramEqs)) varId invariant = do
    case filter (\(p, _) -> p == varId) paramEqs of
      [matchingParamEq] -> do varClone <- createFreshVarFromVar (fst matchingParamEq)
                              let varCloneSubst = createVarSubst [(varId, cstrVar varClone)]
                              return (varClone, cstrAnd (Set.fromList ([guard, invariant, varCloneSubst invariant, cstrEqual (cstrVar varClone) (snd matchingParamEq)])))
      _ -> do return (varId, cstrConst (Cbool False))
-- constructDestSatExpr

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


