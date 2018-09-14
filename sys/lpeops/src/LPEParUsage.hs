{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParUsage
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParUsage (
LPEParamUsage(..),
extractParamUsage,
getParamUsagePerSummand,
getParamSourcesPerSummand,
getParamDestinationsPerSummand,
getUsedParamsPerSummand,
getChangedParamsPerSummand,
getDirectlyUsedParamsPerSummand
) where

import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified FreeVar
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           VarId
import           ValExpr
import           VarFactory
import Constant hiding (sort)

data LPEParamUsage = LPEParamUsage { directlyUsedParams :: [VarId]
                                   , changedParams :: [VarId]
                                   , usedParams :: [VarId]
                                   , rulingParams :: [VarId]
                                   , paramSources :: Map.Map VarId TxsDefs.VExpr
                                   , paramDestinations :: Map.Map VarId TxsDefs.VExpr
                                   }
-- LPEParamUsage

extractParamUsage :: LPESummand -> Map.Map LPESummand LPEParamUsage -> LPEParamUsage
extractParamUsage summand paramUsagePerSummand = Map.findWithDefault (LPEParamUsage [] [] [] [] Map.empty Map.empty) summand paramUsagePerSummand

getParamUsagePerSummand :: [LPESummand] -> [VarId] -> TxsDefs.VExpr -> IOC.IOC (Map.Map LPESummand LPEParamUsage)
getParamUsagePerSummand summands params invariant = do
    let directlyUsedParamsPerSummand = getDirectlyUsedParamsPerSummand summands params
    changedParamsPerSummand <- getChangedParamsPerSummand summands params invariant
    let usedParamsPerSummand = getUsedParamsPerSummand summands directlyUsedParamsPerSummand changedParamsPerSummand
    paramSourcesPerSummand <- getParamSourcesPerSummand summands params invariant
    paramDestinationsPerSummand <- getParamDestinationsPerSummand summands params invariant
    return (Map.fromList (map (\summand -> let summandParamSources = Map.findWithDefault Map.empty summand paramSourcesPerSummand in
                                           let summandParamDestinations = Map.findWithDefault Map.empty summand paramDestinationsPerSummand in
                                             (summand, LPEParamUsage { directlyUsedParams = Map.findWithDefault [] summand directlyUsedParamsPerSummand
                                                                     , changedParams      = Map.findWithDefault [] summand changedParamsPerSummand
                                                                     , usedParams         = Map.findWithDefault [] summand usedParamsPerSummand
                                                                     , rulingParams       = Map.keys (Map.intersection summandParamSources summandParamDestinations)
                                                                     , paramSources       = summandParamSources
                                                                     , paramDestinations  = summandParamDestinations
                                                                     })) summands))
-- getParamUsagePerSummand

getParamSourcesPerSummand :: [LPESummand] -> [VarId] -> TxsDefs.VExpr -> IOC.IOC (Map.Map LPESummand (Map.Map VarId TxsDefs.VExpr))
getParamSourcesPerSummand [] _ _invariant = do return Map.empty
getParamSourcesPerSummand (x:xs) params invariant = do
    parSources <- getParamSources x params
    xs' <- getParamSourcesPerSummand xs params invariant
    return (Map.insert x parSources xs')
  where
    getParamSources :: LPESummand -> [VarId] -> IOC.IOC (Map.Map VarId TxsDefs.VExpr)
    getParamSources _ [] = do return Map.empty
    getParamSources summand@(LPESummand _channelOffers guard _) (p:ps) = do
        ps' <- getParamSources summand ps
        let srcSatExpr = cstrAnd (Set.fromList [guard, invariant])
        srcSolution <- getUniqueSolution srcSatExpr [] [p]
        case srcSolution of
          Just srcSolMap -> do return (Map.insert p (extractVExprFromMap p srcSolMap) ps')
          Nothing -> do return ps'
-- getParamSourcesPerSummand

getParamDestinationsPerSummand :: [LPESummand] -> [VarId] -> TxsDefs.VExpr -> IOC.IOC (Map.Map LPESummand (Map.Map VarId TxsDefs.VExpr))
getParamDestinationsPerSummand [] _ _invariant = do return Map.empty
getParamDestinationsPerSummand (x:xs) params invariant = do
    parDestinations <- getParamDestinations x params
    xs' <- getParamDestinationsPerSummand xs params invariant
    return (Map.insert x parDestinations xs')
  where
    getParamDestinations :: LPESummand -> [VarId] -> IOC.IOC (Map.Map VarId TxsDefs.VExpr)
    getParamDestinations _ [] = do return Map.empty
    getParamDestinations summand (p:ps) = do
        ps' <- getParamDestinations summand ps
        (destVar, destSatExpr) <- constructDestSatExpr summand p invariant
        destSolution <- getUniqueSolution destSatExpr [] [destVar]
        case destSolution of
          Just destSolMap -> do return (Map.insert p (extractVExprFromMap p destSolMap) ps')
          Nothing -> do return ps'
-- getParamDestinationsPerSummand

-- Finds the parameters that are 'used' by the specified summands.
-- A parameter that is 'used' by a summand is one that:
--    + Occurs in the guard, or
--    + Occurs in the assignment to a variable (in the process instantiation).
getUsedParamsPerSummand :: [LPESummand] -> Map.Map LPESummand [VarId] -> Map.Map LPESummand [VarId] -> Map.Map LPESummand [VarId]
getUsedParamsPerSummand [] _directlyUsedParamsPerSummand _changedParamsPerSummand = Map.empty
getUsedParamsPerSummand (x:xs) directlyUsedParamsPerSummand changedParamsPerSummand =
    let usedPars = getUsedParams x in
    let xs' = getUsedParamsPerSummand xs directlyUsedParamsPerSummand changedParamsPerSummand in
      Map.insert x usedPars xs'
  where
    getUsedParams :: LPESummand -> [VarId]
    getUsedParams summand@(LPESummand _channelOffers _guard LPEStop) =
        Map.findWithDefault [] summand directlyUsedParamsPerSummand
    getUsedParams summand@(LPESummand _channelOffers _guard (LPEProcInst paramEqs)) =
        let changedPars = Map.findWithDefault [] summand changedParamsPerSummand in
        let assignments = [expr | changedParam <- changedPars, (assignedParam, expr) <- paramEqs, changedParam == assignedParam ] in
        let indirectlyUsedPars = foldl (\soFar assignment -> Set.union soFar (Set.fromList (FreeVar.freeVars assignment))) Set.empty assignments in
        let directlyUsedPars = Set.fromList (Map.findWithDefault [] summand directlyUsedParamsPerSummand) in
          Set.toList (Set.union indirectlyUsedPars directlyUsedPars)
-- getUsedParamsPerSummand

-- Finds the parameters that are changed by a summand, for all specified summands.
getChangedParamsPerSummand :: [LPESummand] -> [VarId] -> TxsDefs.VExpr -> IOC.IOC (Map.Map LPESummand [VarId])
getChangedParamsPerSummand [] _ _ = do return Map.empty
getChangedParamsPerSummand (x:xs) params invariant = do
    changedPars <- getChangedParams x params
    xs' <- getChangedParamsPerSummand xs params invariant
    return (Map.insert x changedPars xs')
  where
    getChangedParams :: LPESummand -> [VarId] -> IOC.IOC [VarId]
    getChangedParams _summand [] = do return []
    getChangedParams summand (p:ps) = do
        furtherChangedParams <- getChangedParams summand ps
        (destVar, destSatExpr) <- constructDestSatExpr summand p invariant
        taut <- isTautology (cstrAnd (Set.fromList [destSatExpr, cstrEqual (cstrVar destVar) (cstrVar p)]))
        if taut
        then do return furtherChangedParams
        else do return (p:furtherChangedParams)
-- getChangedParamsPerSummand

-- Finds the parameters that are 'directly used' by the specified summands.
-- A parameter that is 'directly used' by a summand is one that occurs in the guard.
getDirectlyUsedParamsPerSummand :: [LPESummand] -> [VarId] -> Map.Map LPESummand [VarId]
getDirectlyUsedParamsPerSummand [] _ = Map.empty
getDirectlyUsedParamsPerSummand (x@(LPESummand _channelOffers guard _):xs) params =
    let guardFreeVars = FreeVar.freeVars guard in
    let directlyUsedPars = Set.intersection (Set.fromList guardFreeVars) (Set.fromList params) in
    let xs' = getDirectlyUsedParamsPerSummand xs params in
      Map.insert x (Set.toList directlyUsedPars) xs'
-- getDirectlyUsedParamsPerSummand

-- The function returns a pair:
--   The first element is the variable for which must be solved in order
--   to determine the value of a parameter after a summand.
--   The second element is the expression with the variable that must be solved.
-- There are two use cases:
--   1. Looking for the value of a parameter after a summand by solving the expression for the variable.
--   2. Determining whether the value of a parameter is unaffected by a summand
--      by checking if 'expression && p2 == p' is a tautology. Here,
--      p2 is the first element in the pair returned by this function, and
--      p1 is the variable provided as the second parameter to this function.
constructDestSatExpr :: LPESummand -> VarId -> TxsDefs.VExpr -> IOC.IOC (VarId, TxsDefs.VExpr)
constructDestSatExpr (LPESummand _ _ LPEStop) varId _invariant = do return (varId, cstrConst (Cbool False))
constructDestSatExpr (LPESummand _channelOffers guard (LPEProcInst paramEqs)) varId invariant = do
    case filter (\(p, _) -> p == varId) paramEqs of
      [matchingParamEq] -> do varClone <- createFreshVarFromVar (fst matchingParamEq)
                              let varCloneSubst = createVarSubst [(varId, cstrVar varClone)]
                              return (varClone, cstrAnd (Set.fromList ([guard, invariant, varCloneSubst invariant, cstrEqual (cstrVar varClone) (snd matchingParamEq)])))
      _ -> do return (varId, cstrConst (Cbool False))
-- constructDestSatExpr

