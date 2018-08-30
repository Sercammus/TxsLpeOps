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
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import           LPEOps
import           LPEParRemoval
import           Satisfiability
import           VarId
import           ValExpr

-- LPE rewrite method.
-- Eliminates parameters that always have the same value from an LPE.
-- State spaces before and after are isomorph.
constElm :: LPEOperation
constElm lpeInstance@((_channels, paramEqs, _summands)) = do
    newLPEInstance <- constElmLoop lpeInstance (map fst paramEqs)
    return (Just newLPEInstance)
-- constElm

-- Core method.
-- Loops until the second argument only contains constant process parameters.
-- Per iteration, runs two nested loops, for guards and for parameter instantiations.
constElmLoop :: LPEInstance          -- LPE from which constants should be eliminated.
             -> [VarId]              -- 'Marked' parameters; that is, process parameters that (for now) are assumed to be constant.
             -> IOC.IOC LPEInstance  -- Resulting LPE.
constElmLoop lpeInstance@(_channels, paramEqs, summands) markedParams = do
    let rho = createVarSubst [(p, v) | p <- markedParams, (q, v) <- paramEqs, p == q]
    newMarkedParams <- constElmGuardCheck summands rho markedParams
    if newMarkedParams == markedParams
    then do removeParsFromLPE markedParams lpeInstance
    else constElmLoop lpeInstance newMarkedParams
-- constElmLoop

-- Checks whether the guard is satisfiable.
-- If it is, the parameter instantiations will never be evaluated anyway and can be ignored!
constElmGuardCheck :: LPESummands                       -- Remaining summands for which the guard must be checked.
                   -> (TxsDefs.VExpr -> TxsDefs.VExpr)  -- Substitution (from marked parameters to their initial values).
                   -> [VarId]                           -- Marked parameters.
                   -> IOC.IOC [VarId]                   -- New marked parameters (cannot grow in size).
constElmGuardCheck [] _ markedParams = do return markedParams
constElmGuardCheck ((LPESummand _ _ LPEStop):xs) rho markedParams = do constElmGuardCheck xs rho markedParams
constElmGuardCheck ((LPESummand _chanOffers guard (LPEProcInst paramEqs)):xs) rho markedParams = do
    unsat <- isUnsatisfiable (rho guard)
    if unsat -- Guard is NOT satisfiable, so leave the marked parameters alone:
    then do constElmGuardCheck xs rho markedParams 
    else do paramInstCheck <- constElmParamEqsCheck paramEqs rho markedParams -- Otherwise, check the parameter equations.
            otherGuardsCheck <- constElmGuardCheck xs rho markedParams
            return (List.intersect paramInstCheck otherGuardsCheck)
-- constElmGuardCheck

-- Checks whether a certain parameter instantiation satisfies the invariant where the parameter equals its initial value.
constElmParamEqsCheck :: LPEParamEqs                       -- Initial values of parameters.
                      -> (TxsDefs.VExpr -> TxsDefs.VExpr)  -- Substitution (from marked parameters to their initial values).
                      -> [VarId]                           -- Marked parameters.
                      -> IOC.IOC [VarId]                   -- New marked parameters (cannot grow in size).
constElmParamEqsCheck _ _ [] = do return []
constElmParamEqsCheck paramEqs rho (markedParam:xs) = do
    case [v | (p, v) <- paramEqs, p == markedParam] of
      [expr] -> do -- Check if rho expr = rho markedParam is a tautology:
                   taut <- isTautology (rho (cstrEqual expr (cstrVar markedParam)))
                   if taut -- Parameter appears to be constant (so far), so keep it around:
                   then do otherParamInstCheck <- constElmParamEqsCheck paramEqs rho xs
                           return (markedParam:otherParamInstCheck)
                   else do --IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Parameter " ++ (Text.unpack (VarId.name markedParam)) ++ " is no longer marked.") ]
                           constElmParamEqsCheck paramEqs rho xs
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_SYSTEM_ERROR ("[Internal error] Parameter has an invalid number of initial values: " ++ (Text.unpack (VarId.name markedParam))) ]
              constElmParamEqsCheck paramEqs rho xs
-- constElmParamEqsCheck



