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

module LPEConstElm (
constElm
) where

import qualified Control.Monad       as Monad
import qualified Data.Map            as Map
import qualified Data.List           as List
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import qualified Subst
import           LPEOps
import           Satisfiability
import           VarId
import           ValExpr
import           SortOf
import           VarFactory

-- Exposed method.
-- Eliminates parameters that always have the same value from an LPE.
constElm :: LPEOperation
constElm lpeInstance@((_channels, paramEqs, _summands)) = do
  newLPEInstance <- constElmLoop lpeInstance (map fst paramEqs)
  return (Just newLPEInstance)

-- Core method.
-- Loops until the second argument only contains constant process parameters.
-- Per iteration, runs two nested loops, for guards and for parameter instantiations.
constElmLoop :: LPEInstance          -- LPE from which constants should be eliminated.
             -> [VarId]              -- 'Marked' parameters; that is, process parameters that (for now) are assumed to be constant.
             -> IOC.IOC LPEInstance  -- Resulting LPE.
constElmLoop lpeInstance [] = do return lpeInstance
constElmLoop lpeInstance@(_channels, paramEqs, summands) markedParams =
    let rho = \e -> Subst.subst (Map.fromList [(p, v) | p <- markedParams, (q, v) <- paramEqs, p == q]) Map.empty (e :: TxsDefs.VExpr) in
      do newMarkedParams <- constElmGuardCheck summands rho markedParams
         if newMarkedParams == markedParams
         then paramElm lpeInstance markedParams
         else constElmLoop lpeInstance newMarkedParams
-- constElmLoop

-- Checks whether the guard is satisfiable.
-- If it is, the parameter instantiations will never be evaluated anyway and can be ignored!
constElmGuardCheck :: LPESummands                       -- Remaining summands for which the guard must be checked.
                   -> (TxsDefs.VExpr -> TxsDefs.VExpr)  -- Substitution (from marked parameters to their initial values).
                   -> [VarId]                           -- Marked parameters.
                   -> IOC.IOC [VarId]                   -- New marked parameters (cannot grow in size).
constElmGuardCheck [] _ markedParams = do return markedParams
constElmGuardCheck (summand:xs) rho markedParams =
    case summand of
      LPEStopSummand -> do constElmGuardCheck xs rho markedParams
      LPESummand _chanOffers guard paramEqs -> do
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
constElmParamEqsCheck paramEqs rho (markedParam:xs) =
    case [v | (p, v) <- paramEqs, p == markedParam] of
      [expr] -> do
                  -- Check if rho expr = rho markedParam is an invariant:
                  invariant <- isInvariant (rho $ cstrEqual expr (cstrVar markedParam))
                  if invariant -- Parameter appears to be constant (so far), so keep it around:
                  then do otherParamInstCheck <- constElmParamEqsCheck paramEqs rho xs
                          return (markedParam:otherParamInstCheck)
                  else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Parameter " ++ (show markedParam) ++ " is no longer marked.") ]
                          constElmParamEqsCheck paramEqs rho xs
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_SYSTEM_ERROR ("[Internal error] Parameter has an invalid number of initial values: " ++ (show markedParam)) ]
              constElmParamEqsCheck paramEqs rho xs
-- constElmParamEqsCheck

-- Helper method.
-- Eliminates the specified parameters an LPE.
-- Occurrences of the parameters in expressions are substituted by their initial values.
paramElm :: LPEInstance -> [VarId] -> IOC.IOC LPEInstance
paramElm (channels, paramEqs, summands) targetParams = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Eliminating parameter(s): " ++ (show targetParams)) ]
    newSummands <- Monad.foldM summandParamElm [] summands
    return (channels, newParamEqs, newSummands)
  where
    -- Eliminates parameters from a series of parameter instantiations:
    paramEqsParamElm :: LPEParamEqs -> LPEParamEqs
    paramEqsParamElm eqs = [(p, rho v) | (p, v) <- eqs, not (p `elem` targetParams)]
    
    -- Parameter instantiation for the new process:
    newParamEqs = paramEqsParamElm paramEqs
    
    -- Substitution only for the parameters that are being eliminated:
    rho = \e -> Subst.subst (Map.fromList newParamEqs) Map.empty (e :: TxsDefs.VExpr)
    
    -- Eliminates parameters from a summand:
    summandParamElm :: LPESummands -> LPESummand -> IOC.IOC LPESummands
    summandParamElm soFar LPEStopSummand = do return (soFar ++ [LPEStopSummand])
    summandParamElm soFar (LPESummand channelOffers guard eqs) = do
        newChannelOffers <- Monad.foldM channelOfferParamElm [] channelOffers
        return (soFar ++ [LPESummand newChannelOffers (rho guard) (paramEqsParamElm eqs)])
    
    -- Eliminates parameters from channel offers:
    channelOfferParamElm :: LPEChannelOffers -> LPEChannelOffer -> IOC.IOC LPEChannelOffers
    channelOfferParamElm soFar (chanId, vars) = do newVars <- Monad.foldM channelVarParamElm [] vars
                                                   return (soFar ++ [(chanId, newVars)])
    
    -- Eliminates parameters from channel variables:
    channelVarParamElm :: [VarId] -> VarId -> IOC.IOC [VarId]
    channelVarParamElm soFar var = if var `elem` targetParams
                                   then do newVar <- createFreshVar (sortOf var)
                                           return (soFar ++ [newVar])
                                   else do return (soFar ++ [var])
-- paramElm























