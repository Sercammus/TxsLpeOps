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

import qualified Data.List           as List
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import           LPEOps
import           LPEParRemoval
import           Satisfiability
import           VarId
import           ValExpr
import           Constant

-- LPE rewrite method.
-- Eliminates parameters that always have the same value from an LPE.
-- State spaces before and after are isomorph.
constElm :: LPEOperation
constElm lpeInstance@((_channels, paramEqs, _summands)) _out invariant = do
    newLPEInstance <- constElmLoop lpeInstance invariant (map fst paramEqs)
    return (Right newLPEInstance)
-- constElm

-- Core method.
-- Loops until the second argument only contains constant process parameters.
-- Per iteration, runs two nested loops, for guards and for parameter instantiations.
constElmLoop :: LPEInstance          -- LPE from which constants should be eliminated.
             -> TxsDefs.VExpr        -- Invariant.
             -> [VarId]              -- 'Marked' parameters; that is, process parameters that (for now) are assumed to be constant.
             -> IOC.IOC LPEInstance  -- Resulting LPE.
constElmLoop lpeInstance@(_channels, paramEqs, summands) invariant markedParams = do
    let rho = createVarSubst [(p, v) | p <- markedParams, (q, v) <- paramEqs, p == q]
    newMarkedParams <- constElmPerSummand summands invariant rho markedParams
    if newMarkedParams == markedParams
    then do removeParsFromLPE markedParams lpeInstance
    else constElmLoop lpeInstance invariant newMarkedParams
-- constElmLoop

-- Checks whether the guard is satisfiable.
-- If it is, the parameter instantiations will never be evaluated anyway and can be ignored!
constElmPerSummand :: LPESummands                       -- Remaining summands for which the guard must be checked.
                   -> TxsDefs.VExpr                     -- Invariant.
                   -> (TxsDefs.VExpr -> TxsDefs.VExpr)  -- Substitution (from marked parameters to their initial values).
                   -> [VarId]                           -- Marked parameters.
                   -> IOC.IOC [VarId]                   -- New marked parameters (cannot grow in size).
constElmPerSummand [] _ _ markedParams = do return markedParams
constElmPerSummand ((LPESummand _ _ _ LPEStop):xs) invariant rho markedParams = do constElmPerSummand xs invariant rho markedParams
constElmPerSummand ((LPESummand _ _ guard (LPEProcInst paramEqs)):xs) invariant rho markedParams = do
    paramInstCheck <- constElmPerMarkedParam paramEqs invariant guard rho markedParams -- Otherwise, check the parameter equations.
    otherGuardsCheck <- constElmPerSummand xs invariant rho markedParams
    return (List.intersect paramInstCheck otherGuardsCheck)
-- constElmPerSummand

-- Checks whether a certain parameter instantiation satisfies the invariant where the parameter equals its initial value.
constElmPerMarkedParam :: LPEParamEqs                       -- Initial values of parameters.
                       -> TxsDefs.VExpr                     -- Invariant.
                       -> TxsDefs.VExpr                     -- Guard.
                       -> (TxsDefs.VExpr -> TxsDefs.VExpr)  -- Substitution (from marked parameters to their initial values).
                       -> [VarId]                           -- Marked parameters.
                       -> IOC.IOC [VarId]                   -- New marked parameters (cannot grow in size).
constElmPerMarkedParam _ _ _ _ [] = do return []
constElmPerMarkedParam paramEqs invariant guard rho (markedParam:xs) = do
    case [v | (p, v) <- paramEqs, p == markedParam] of
      [expr] -> do -- Check if (IF guard THEN expr = markedParam ELSE true ENDIF)[rho] is a tautology:
                   taut <- isTautology (rho (cstrAnd (Set.fromList [invariant, cstrITE guard (cstrEqual expr (cstrVar markedParam)) (cstrConst (Cbool True))])))
                   if taut -- Parameter appears to be constant (so far), so keep it around:
                   then do otherParamInstCheck <- constElmPerMarkedParam paramEqs invariant guard rho xs
                           return (markedParam:otherParamInstCheck)
                   else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Parameter " ++ (Text.unpack (VarId.name markedParam)) ++ " is no longer marked.") ]
                           constElmPerMarkedParam paramEqs invariant guard rho xs
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_SYSTEM_ERROR ("[Internal error] Parameter has an invalid number of initial values: " ++ (Text.unpack (VarId.name markedParam))) ]
              constElmPerMarkedParam paramEqs invariant guard rho xs
-- constElmPerMarkedParam



