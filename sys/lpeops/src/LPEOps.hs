{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEOps
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEOps (
lpeOpsVersion,
LPEOperation,
lpeOperations,
discardLPE,
showLPE,
module LPETypes
) where

import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import           LPETypes
import           LPEPrettyPrint

lpeOpsVersion :: String
lpeOpsVersion = "0.2.0"

-- An LPE operation takes:
--  - An input LPE;
--  - An output name (for a file or a new model);
--  - An invariant (using 'True' should have no effect);
-- An LPE operation yields either
--  - A list of (error) messages, in case there was a problem or some other event happened; or
--  - A new LPE instance.
type LPEOperation = LPEInstance -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] LPEInstance)

-- Core method that does the following:
--  1. Transforms a closed process expression to an LPE instance;
--  2. Applies the given operation to the LPE instance, which results in a new LPE instance;
--  3. Transforms the new LPE instance to a process definition with the specified name and
--     a process expression that creates an instance of this process definition.
lpeOperations :: [LPEOperation] -> TxsDefs.BExpr -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef))
lpeOperations operations procInst out invariant = do
    eitherLPEInstance <- toLPEInstance procInst
    case eitherLPEInstance of
      Left msgs -> do return (Left msgs)
      Right lpeInstance -> do eitherNewLPEInstance <- lpeOperation operations lpeInstance out invariant
                              case eitherNewLPEInstance of
                                Left msgs -> do return (Left msgs)
                                Right newLPEInstance -> do temp <- fromLPEInstance newLPEInstance out
                                                           return (Right temp)
-- lpeOperations

lpeOperation :: [LPEOperation] -> LPEInstance -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] LPEInstance)
lpeOperation [] lpeInstance _out _invariant = do return (Right lpeInstance)
lpeOperation (x:xs) lpeInstance out invariant = do
    eitherNewLPEInstance <- x lpeInstance out invariant
    case eitherNewLPEInstance of
      Left msgs -> do return (Left msgs)
      Right newLPEInstance -> do lpeOperation xs newLPEInstance out invariant
-- lpeOperations

discardLPE :: LPEOperation
discardLPE _lpeInstance _out _invariant = do return (Left ["LPE discarded!"])

showLPE :: LPEOperation
showLPE lpeInstance _out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY (showLPEInstance lpeInstance) ]
    return (Right lpeInstance)
-- showLPE


