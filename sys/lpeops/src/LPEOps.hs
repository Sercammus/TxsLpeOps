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
import           Name
import           LPEPrettyPrint

type LPEOperation = LPEInstance -> TxsDefs.VExpr -> IOC.IOC (Either LPEInstance String)

-- Core method that does the following:
--  1. Transforms a closed process expression to an LPE instance;
--  2. Applies the given operation to the LPE instance, which results in a new LPE instance;
--  3. Transforms the new LPE instance to a process definition with the specified name and
--     a process expression that creates an instance of this process definition.
lpeOperations :: [LPEOperation] -> TxsDefs.BExpr -> TxsDefs.VExpr -> Name -> IOC.IOC (Either (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef) String)
lpeOperations operations procInst invariant name = do
    maybeLPEInstance <- toLPEInstance procInst
    case maybeLPEInstance of
      Just lpeInstance -> do eitherNewLPEInstance <- lpeOperation operations lpeInstance invariant
                             case eitherNewLPEInstance of
                               Left newLPEInstance -> do temp <- fromLPEInstance newLPEInstance name
                                                         return (Left temp)
                               Right msg -> do return (Right msg)
      Nothing -> do return (Right "Invalid LPE format!")
-- lpeOperations

lpeOperation :: [LPEOperation] -> LPEInstance -> TxsDefs.VExpr -> IOC.IOC (Either LPEInstance String)
lpeOperation [] lpeInstance _invariant = do return (Left lpeInstance)
lpeOperation (x:xs) lpeInstance invariant = do
    eitherNewLPEInstance <- x lpeInstance invariant
    case eitherNewLPEInstance of
      Left newLPEInstance -> do lpeOperation xs newLPEInstance invariant
      Right msg -> do return (Right msg)
-- lpeOperations

discardLPE :: LPEOperation
discardLPE _lpeInstance _invariant = do return (Right "LPE discarded!")

showLPE :: LPEOperation
showLPE lpeInstance _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY (showLPEInstance lpeInstance) ]
    return (Left lpeInstance)
-- showLPE


