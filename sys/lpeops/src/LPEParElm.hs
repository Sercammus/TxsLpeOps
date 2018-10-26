{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParElm
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParElm (
parElm
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified FreeVar
import qualified VarId
import LPEOps
import LPEParRemoval

-- Eliminates inert parameters (=parameters that do not contribute to the behavior of a process) from an LPE:
parElm :: LPEOperation
parElm lpeInstance@((_channels, paramEqs, summands)) _out _invariant = do
    let allParams = Set.fromList (Map.keys paramEqs)
    let guardParams = Set.unions (map (Set.fromList . FreeVar.freeVars . getGuard) summands)
    -- All parameters are initially assumed to be inert, except those used in a guard.
    -- This initial set of inert parameters is reduced until a fixpoint is reached:
    let inertParams = getInertParams lpeInstance (allParams Set.\\ guardParams)
    -- The remaining inert parameters are removed from the LPE:
    newLPE <- removeParsFromLPE inertParams lpeInstance
    return (Right newLPE)
  where
    getGuard :: LPESummand -> TxsDefs.VExpr
    getGuard (LPESummand _ _ guard _) = guard
-- parElm

-- Loops until no more parameters are removed to the set of (presumably) inert parameters:
getInertParams :: LPEInstance -> Set.Set VarId.VarId -> Set.Set VarId.VarId
getInertParams lpeInstance@(_channels, _paramEqs, summands) inertParams =
    let newInertParams = removeVarsAssignedToNonInertParams summands inertParams in
      if newInertParams /= inertParams
      then getInertParams lpeInstance newInertParams
      else newInertParams
-- getInertParams

-- Removes from the set of inert parameter all variables (=superset of parameters) that are assigned to parameters that are NOT inert:
removeVarsAssignedToNonInertParams :: LPESummands -> Set.Set VarId.VarId -> Set.Set VarId.VarId
removeVarsAssignedToNonInertParams summands inertParams =
    inertParams Set.\\ (Set.unions (map (getParamsAssignedToNonInertParams inertParams) summands))
  where
    getParamsAssignedToNonInertParams :: Set.Set VarId.VarId -> LPESummand -> Set.Set VarId.VarId
    getParamsAssignedToNonInertParams _ (LPESummand _ _ _ LPEStop) = Set.empty
    getParamsAssignedToNonInertParams iparams (LPESummand _ _ _ (LPEProcInst paramEqs)) =
        Set.unions (map (\(p, v) -> if Set.member p iparams then Set.empty else Set.fromList (FreeVar.freeVars v)) (Map.toList paramEqs))
-- parElmForAllSummands

