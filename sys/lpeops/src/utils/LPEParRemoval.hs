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
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import qualified Subst
import           LPEOps
import           VarId

-- Removes the specified parameters an LPE.
-- Occurrences of the parameters in expressions are substituted by their initial values.
removeParsFromLPE :: [VarId] -> LPEInstance -> IOC.IOC LPEInstance
removeParsFromLPE [] lpeInstance = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "No LPE parameters have been listed for removal!" ]
    return lpeInstance
removeParsFromLPE targetParams (channels, paramEqs, summands) = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Removing the following LPE parameters:" ]
    Monad.mapM_ (\p -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("\t" ++ (Text.unpack (VarId.name p))) ]) targetParams
    let newParamEqs = Map.restrictKeys (Set.fromList targetParams) paramEqs
    let rho = \e -> Subst.subst (Map.fromList [(p, v) | (p, v) <- paramEqs, p `elem` targetParams]) Map.empty (e :: TxsDefs.VExpr)
    newSummands <- Monad.mapM removeParsFromSummand summands
    return (channels, newParamEqs, newSummands)
  where
    -- Eliminates parameters from a summand.
    -- Note that channel variables are always fresh, and therefore do not have to be substituted:
    removeParsFromSummand :: LPESummand -> IOC.IOC LPESummand
    removeParsFromSummand (LPESummand channelVars channelOffers guard procInst) = do
        return (LPESummand channelVars channelOffers (rho guard) (removeParsFromProcInst procInst))
    
    -- Eliminates parameters from a process instantiation:
    removeParsFromProcInst :: LPEProcInst -> LPEProcInst
    removeParsFromProcInst (LPEProcInst eqs) = LPEProcInst (Map.restrictKeys (Set.fromList targetParams) paramEqs)
    removeParsFromProcInst LPEStop = LPEStop
-- removeParsFromLPE























