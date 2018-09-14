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

import qualified Data.List           as List
import qualified EnvCore             as IOC
import qualified FreeVar
import           LPEOps
import           LPEParRemoval
import           Satisfiability
import           VarId

-- LPE rewrite method.
-- Eliminates parameters that do not contribute to the behavior of a process from an LPE.
-- State spaces before and after are isomorph.
parElm :: LPEOperation
parElm lpeInstance@((_channels, paramEqs, summands)) _invariant = do
    let inertParams = foldl filterInertParamsWithSummand (map fst paramEqs) summands
    newLPEInstance <- parElmLoop lpeInstance inertParams
    return (Just newLPEInstance)
-- parElm

-- Eliminate parameters from a list if they are used in the guard or channel communications of a given summand:
filterInertParamsWithSummand :: [VarId] -> LPESummand -> [VarId]
filterInertParamsWithSummand soFar (LPESummand channelOffers guard _procInst) =
    let channelOfferVars = foldl (++) [] (map snd channelOffers) in
      (soFar List.\\ channelOfferVars) List.\\ (FreeVar.freeVars guard)
-- filterInertParamsWithSummand

-- Core method.
-- Loops until the second argument only contains inert process parameters.
-- Per iteration, runs two nested loops, for guards and for parameter instantiations.
parElmLoop :: LPEInstance          -- LPE from which inert parameters should be eliminated.
           -> [VarId]              -- 'Marked' parameters; that is, process parameters that (for now) are assumed to be inert.
           -> IOC.IOC LPEInstance  -- Resulting LPE.
parElmLoop lpeInstance@(_channels, _paramEqs, summands) inertParams = do
    newInertParams <- parElmCheck summands inertParams
    if newInertParams == inertParams
    then removeParsFromLPE inertParams lpeInstance
    else parElmLoop lpeInstance newInertParams
-- parElmLoop

-- Checks whether the guard is satisfiable.
-- If it is, the parameter instantiations will never be evaluated anyway and can be ignored!
parElmCheck :: LPESummands                       -- Remaining summands for which the recursion must be checked.
            -> [VarId]                           -- Marked parameters.
            -> IOC.IOC [VarId]                   -- New marked parameters (cannot grow in size).
parElmCheck [] inertParams = do return inertParams
parElmCheck ((LPESummand _ _ LPEStop):xs) inertParams = do parElmCheck xs inertParams
parElmCheck ((LPESummand _chanOffers guard (LPEProcInst paramEqs)):xs) inertParams = do
    unsat <- isNotSatisfiable guard
    if unsat -- Guard is NOT satisfiable, so leave the marked parameters alone:
    then do parElmCheck xs inertParams
    else do parElmCheck xs (foldl filterInertParamsWithEq inertParams paramEqs)
  where
    filterInertParamsWithEq :: [VarId] -> LPEParamEq -> [VarId]
    filterInertParamsWithEq soFar (var, expr) = if (elem var inertParams) then soFar else (soFar List.\\ (FreeVar.freeVars expr))
-- parElmCheck



