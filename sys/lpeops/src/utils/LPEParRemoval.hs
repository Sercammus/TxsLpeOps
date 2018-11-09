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
import           LPEOps
import           BlindSubst
import           VarId

-- Removes the specified parameters an LPE.
-- Occurrences of the parameters in expressions are substituted by their initial values.
removeParsFromLPE :: Set.Set VarId -> LPEInstance -> IOC.IOC LPEInstance
removeParsFromLPE targetParams lpeInstance@(channels, paramEqs, summands)
    | targetParams == Set.empty =
        return lpeInstance
    | otherwise = do
        Monad.mapM_ (\p -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Removed parameter " ++ Text.unpack (VarId.name p)) ]) (Set.toList targetParams)
        let rho = Map.restrictKeys paramEqs targetParams
        newSummands <- Monad.mapM (removeParsFromSummand rho) (Set.toList summands)
        return (channels, Map.withoutKeys paramEqs targetParams, Set.fromList newSummands)
  where
    -- Eliminates parameters from a summand.
    -- Note that channel variables are always fresh, and therefore do not have to be substituted:
    removeParsFromSummand :: Map.Map VarId TxsDefs.VExpr -> LPESummand -> IOC.IOC LPESummand
    removeParsFromSummand rho contextSummand@(LPESummand channelVars channelOffers guard procInst) = do
        guard' <- doConfidentSubst contextSummand rho guard
        procInst' <- removeParsFromProcInst contextSummand rho procInst
        return (LPESummand channelVars channelOffers guard' procInst')
    
    -- Eliminates parameters from a process instantiation:
    removeParsFromProcInst :: LPESummand -> Map.Map VarId TxsDefs.VExpr -> LPEProcInst -> IOC.IOC LPEProcInst
    removeParsFromProcInst contextSummand rho (LPEProcInst eqs) = do
        let withoutTargetParams = Map.toList (Map.withoutKeys eqs targetParams)
        newAssignments <- Monad.mapM (doConfidentSubst contextSummand rho . snd) withoutTargetParams
        let newEqs = Map.fromList (zip (map fst withoutTargetParams) newAssignments)
        return (LPEProcInst newEqs)
    removeParsFromProcInst _ _ LPEStop = return LPEStop
-- removeParsFromLPE


