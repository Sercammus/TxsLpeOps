{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEConstElm
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module LPEConstElm (
constElm
) where

import qualified Control.Monad       as Monad
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified TxsDefs
import           LPEOps
import           LPEParRemoval
import           Satisfiability
import           VarId
import           ValExpr hiding (subst)
import           Constant

-- LPE rewrite method.
-- Eliminates parameters that always have the same value from an LPE.
-- State spaces before and after are isomorph.
constElm :: LPEOperation
constElm lpe@((_channels, initParamEqs, _summands)) _out invariant = do
    constParams <- getConstParams lpe invariant (Map.keysSet initParamEqs)
    newLPE <- removeParsFromLPE constParams lpe
    return (Right newLPE)
-- constElm

getConstParams :: LPEInstance -> TxsDefs.VExpr -> Set.Set VarId -> IOC.IOC (Set.Set VarId)
getConstParams lpe invariant constParams = do
    newConstParams <- getConstParamsForAllSummands lpe invariant constParams
    if newConstParams /= constParams
    then getConstParams lpe invariant newConstParams
    else return newConstParams
-- getConstParams

getConstParamsForAllSummands :: LPEInstance -> TxsDefs.VExpr -> Set.Set VarId -> IOC.IOC (Set.Set VarId)
getConstParamsForAllSummands (_channels, initParamEqs, summands) invariant constParams = do
    let subst = Map.restrictKeys initParamEqs constParams
    constParamsPerSummand <- Monad.mapM (getConstParamsForSummand subst invariant constParams) summands
    return (foldl Set.intersection constParams constParamsPerSummand)
-- getConstParamsForAllSummands

getConstParamsForSummand :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> Set.Set VarId -> LPESummand -> IOC.IOC (Set.Set VarId)
getConstParamsForSummand subst invariant constParams summand = do
    result <- Monad.mapM (isConstParamForSummand subst invariant summand) (Set.toList constParams)
    return (Set.unions result)
-- getConstParamsForSummand

isConstParamForSummand :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> LPESummand -> VarId -> IOC.IOC (Set.Set VarId)
isConstParamForSummand _ _ (LPESummand _ _ _ LPEStop) _ = do return Set.empty
isConstParamForSummand subst invariant (LPESummand _ _ guard (LPEProcInst paramEqs)) testParam = do
    let expr = cstrITE guard (cstrEqual (paramEqs Map.! testParam) (cstrVar testParam)) (cstrConst (Cbool True))
    expr' <- doBlindSubst subst expr
    taut <- isTautology expr' invariant
    if taut
    then return (Set.singleton testParam)
    else return Set.empty
-- isConstParamsForSummand


