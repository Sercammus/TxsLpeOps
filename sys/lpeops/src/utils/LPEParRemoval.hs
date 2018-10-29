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
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import qualified Subst
import           LPEOps
import           VarId

-- Removes the specified parameters an LPE.
-- Occurrences of the parameters in expressions are substituted by their initial values.
removeParsFromLPE :: Set.Set VarId -> LPEInstance -> IOC.IOC LPEInstance
removeParsFromLPE targetParams lpeInstance@(channels, paramEqs, summands)
    | targetParams == Set.empty = do
        return lpeInstance
    | otherwise = do
        Monad.mapM_ (\p -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Removed parameter " ++ (Text.unpack (VarId.name p))) ]) (Set.toList targetParams)
        let rho = \e -> Subst.subst (Map.restrictKeys paramEqs targetParams) Map.empty (e :: TxsDefs.VExpr)
        newSummands <- Monad.mapM (removeParsFromSummand rho) summands
        return (channels, Map.withoutKeys paramEqs targetParams, newSummands)
  where
    -- Eliminates parameters from a summand.
    -- Note that channel variables are always fresh, and therefore do not have to be substituted:
    removeParsFromSummand :: (TxsDefs.VExpr -> TxsDefs.VExpr) -> LPESummand -> IOC.IOC LPESummand
    removeParsFromSummand rho (LPESummand channelVars channelOffers guard procInst) = do
        return (LPESummand channelVars channelOffers (rho guard) (removeParsFromProcInst rho procInst))
    
    -- Eliminates parameters from a process instantiation:
    removeParsFromProcInst :: (TxsDefs.VExpr -> TxsDefs.VExpr) -> LPEProcInst -> LPEProcInst
    removeParsFromProcInst rho (LPEProcInst eqs) = LPEProcInst (Map.map rho (Map.withoutKeys eqs targetParams))
    removeParsFromProcInst _ LPEStop = LPEStop
-- removeParsFromLPE























