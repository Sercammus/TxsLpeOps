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
dummyOp,
module LPETypes
) where

import qualified EnvCore as IOC
import qualified TxsDefs
import           LPETypes
import           Name

type LPEOperation = LPEInstance -> TxsDefs.VExpr -> IOC.IOC (Maybe LPEInstance)

-- Core method that does the following:
--  1. Transforms a closed process expression to an LPE instance;
--  2. Applies the given operation to the LPE instance, which results in a new LPE instance;
--  3. Transforms the new LPE instance to a process definition with the specified name and
--     a process expression that creates an instance of this process definition.
lpeOperations :: [LPEOperation] -> TxsDefs.BExpr -> TxsDefs.VExpr -> Name -> IOC.IOC (Maybe (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef))
lpeOperations operations procInst invariant name = do
    maybeLPEInstance <- toLPEInstance procInst
    case maybeLPEInstance of
      Just lpeInstance -> do maybeNewLPEInstance <- lpeOperation operations lpeInstance invariant
                             case maybeNewLPEInstance of
                               Just newLPEInstance -> do temp <- fromLPEInstance newLPEInstance name
                                                         return (Just temp)
                               Nothing -> do return Nothing
      Nothing -> do return Nothing
-- lpeOperations

lpeOperation :: [LPEOperation] -> LPEInstance -> TxsDefs.VExpr -> IOC.IOC (Maybe LPEInstance)
lpeOperation [] lpeInstance _invariant = do return (Just lpeInstance)
lpeOperation (x:xs) lpeInstance invariant = do
    maybeNewLPEInstance <- x lpeInstance invariant
    case maybeNewLPEInstance of
      Just newLPEInstance -> do lpeOperation xs newLPEInstance invariant
      Nothing -> do return Nothing
-- lpeOperations

dummyOp :: LPEOperation
dummyOp lpeInstance _invariant = do return (Just lpeInstance)




