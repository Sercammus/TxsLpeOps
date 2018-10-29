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
        IOC.putMsgs [ EnvData.TXS_CORE_ANY "No LPE parameters have been listed for removal!" ]
        return lpeInstance
    | otherwise = do
        IOC.putMsgs [ EnvData.TXS_CORE_ANY "Removing the following parameters:" ]
        Monad.mapM_ (\p -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("\t" ++ (Text.unpack (VarId.name p))) ]) (Set.toList targetParams)
        let rho = \e -> Subst.subst (Map.restrictKeys paramEqs targetParams) Map.empty (e :: TxsDefs.VExpr)
        newSummands <- Monad.mapM (removeParsFromSummand rho) summands
        -- let allParams = Set.fromList (concat [getParams s | s <- newSummands])
        -- let shouldBeEmpty = Set.intersection allParams targetParams
        -- Monad.mapM_ (\p -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("BAD BAD BAD variable is still used: " ++ (Text.unpack (VarId.name p))) ]) (Set.toList shouldBeEmpty)
        -- let sbe2 = Set.intersection (Map.keysSet (Map.withoutKeys paramEqs targetParams)) targetParams
        -- Monad.mapM_ (\p -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("BAD2 BAD2 BAD2 variable is still used: " ++ (Text.unpack (VarId.name p))) ]) (Set.toList sbe2)
        return (channels, Map.withoutKeys paramEqs targetParams, newSummands)
  where
    -- getParams :: LPESummand -> [VarId]
    -- getParams (LPESummand _ _ _ (LPEProcInst eqs)) = Map.keys eqs
    -- getParams _ = []
    
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























