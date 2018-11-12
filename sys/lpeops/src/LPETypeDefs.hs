{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPETypes
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPETypeDefs (
LPEInstance,
LPESummand(..),
LPESummands,
LPEProcInst(..),
LPEChannelOffer,
LPEChannelOffers,
LPEParamEqs
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import           VarId

-- Type around which this module revolves.
-- It consists of the following parts:
--  - Channels used by the LPE (included mostly so that conversion to TXS is possible without additional channel information).
--  - Parameters used by the LPE and their initial values (each pair forms a 'parameter equation').
--  - List of summands of the LPE.
type LPEInstance = ([TxsDefs.ChanId], LPEParamEqs, LPESummands)

-- Main building block of an LPE.
-- Each summand provides the following pieces of critical information:
--  - All channel variables, including hidden variables.
--  - Channel offers (action prefices and the *fresh* variables - also found in the earlier list - used per action prefix for synchronization).
--  - Guard (restriction on when the summand can be 'applied').
--  - STOP, or a number of parameter equations to be used for the recursive instantiation.
data LPESummand = LPESummand [VarId] LPEChannelOffers TxsDefs.VExpr LPEProcInst deriving (Eq, Ord, Show)
type LPESummands = Set.Set LPESummand

-- Summands can end with a recursive instantiation of the LPE or with a STOP:
data LPEProcInst = LPEStop | LPEProcInst LPEParamEqs deriving (Eq, Ord, Show)

-- Convenience type.
-- Relates a channel with communication variables over which that channel must be synchronized.
type LPEChannelOffer = (TxsDefs.ChanId, [VarId])
type LPEChannelOffers = [LPEChannelOffer]

-- Convenience type.
-- Relates a parameter with the (initial) value of that parameter
-- (in the case of a particular process instantiation).
type LPEParamEqs = Map.Map VarId TxsDefs.VExpr

