  {-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParRemoval
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParRemoval (
removeParsFromLPE
) where

import qualified Control.Monad       as Monad
import qualified Data.Map            as Map
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import qualified Subst
import           LPEOps
import           VarId
import           SortOf
import           VarFactory

-- Removes the specified parameters an LPE.
-- Occurrences of the parameters in expressions are substituted by their initial values.
removeParsFromLPE :: [VarId] -> LPEInstance -> IOC.IOC LPEInstance
removeParsFromLPE targetParams (channels, paramEqs, summands) = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Eliminating parameter(s): " ++ (show targetParams)) ]
    let newParamEqs = [(p, v) | (p, v) <- paramEqs, not (p `elem` targetParams)]
    newSummands <- Monad.foldM removeParsFromSummand [] summands
    return (channels, newParamEqs, newSummands)
  where
    -- Substitution only for the parameters that are being eliminated:
    rho = \e -> Subst.subst (Map.fromList [(p, v) | (p, v) <- paramEqs, p `elem` targetParams]) Map.empty (e :: TxsDefs.VExpr)
    
    -- Eliminates parameters from a series of parameter instantiations:
    removeParsFromParamEqs :: LPEParamEqs -> LPEParamEqs
    removeParsFromParamEqs eqs = [(p, rho v) | (p, v) <- eqs, not (p `elem` targetParams)]
    
    -- Eliminates parameters from a summand:
    removeParsFromSummand :: LPESummands -> LPESummand -> IOC.IOC LPESummands
    removeParsFromSummand soFar LPEStopSummand = do return (soFar ++ [LPEStopSummand])
    removeParsFromSummand soFar (LPESummand channelOffers guard eqs) = do
        newChannelOffers <- Monad.foldM removeParsFromChannelOffer [] channelOffers
        return (soFar ++ [LPESummand newChannelOffers (rho guard) (removeParsFromParamEqs eqs)])
    
    -- Eliminates parameters from channel offers:
    removeParsFromChannelOffer :: LPEChannelOffers -> LPEChannelOffer -> IOC.IOC LPEChannelOffers
    removeParsFromChannelOffer soFar (chanId, vars) = do newVars <- Monad.foldM removeParsFromChannelVar [] vars
                                                         return (soFar ++ [(chanId, newVars)])
    
    -- Eliminates parameters from channel variables:
    removeParsFromChannelVar :: [VarId] -> VarId -> IOC.IOC [VarId]
    removeParsFromChannelVar soFar var = if var `elem` targetParams
                                         then do newVar <- createFreshVar (sortOf var)
                                                 return (soFar ++ [newVar])
                                         else do return (soFar ++ [var])
-- removeParsFromLPE























