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
LPEOp(..),
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
lpeOpsVersion = "0.7.6"

data LPEOp = LPEOpLoop | LPEOp LPEOperation

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
lpeOperations :: [LPEOp] -> TxsDefs.BExpr -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef))
lpeOperations operations procInst out invariant = do
    eitherLPEInstance <- toLPEInstance procInst
    case eitherLPEInstance of
      Left msgs -> return (Left msgs)
      Right lpeInstance -> do eitherNewLPEInstances <- lpeOperation operations operations [lpeInstance, lpeInstance] out invariant
                              case eitherNewLPEInstances of
                                Left msgs -> return (Left msgs)
                                Right [] -> return (Left ["No output LPE found!"])
                                Right (newLPE:_) -> do temp <- fromLPEInstance newLPE out
                                                       if newLPE /= lpeInstance
                                                       then IOC.putMsgs [ EnvData.TXS_CORE_ANY "LPE instance has been rewritten!" ]
                                                       else IOC.putMsgs [ EnvData.TXS_CORE_ANY "LPE instance is identical to input!" ]
                                                       return (Right temp)
-- lpeOperations

lpeOperation :: [LPEOp] -> [LPEOp] -> [LPEInstance] -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] [LPEInstance])
lpeOperation _ops _ [] _out _invariant = return (Left ["No input LPE found!"])
lpeOperation _ops [] lpeInstances _out _invariant = return (Right lpeInstances)
lpeOperation ops (LPEOpLoop:xs) (lpeInstance:ys) out invariant =
    if lpeInstance `elem` ys
    then lpeOperation ops xs (lpeInstance:ys) out invariant
    else lpeOperation ops ops (lpeInstance:lpeInstance:ys) out invariant
lpeOperation ops (LPEOp op:xs) (lpeInstance:ys) out invariant = do
    eitherNewLPEInstance <- op lpeInstance out invariant
    case eitherNewLPEInstance of
      Left msgs -> return (Left msgs)
      Right newLPE -> let scopeProblems = getScopeProblems newLPE in
                        if null scopeProblems
                        then lpeOperation ops xs (newLPE:ys) out invariant
                        else return (Left scopeProblems)
-- lpeOperation

discardLPE :: LPEOperation
discardLPE _lpeInstance _out _invariant = return (Left ["LPE discarded!"])

showLPE :: LPEOperation
showLPE lpeInstance _out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY (showLPEInstance lpeInstance) ]
    return (Right lpeInstance)
-- showLPE


