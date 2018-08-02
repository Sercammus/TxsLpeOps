{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TXS2MCRL2Env
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module TXS2MCRL2Env (
T2MMonad,
T2MRegisteredObject(..),
T2MEnv(..),
modifySpec,
registerObject,
getRegisteredSort,
getRegisteredCstr,
getRegisteredVar,
getRegisteredMapping,
getRegisteredAction,
getRegisteredProcess,
getFreshName
) where

import qualified Data.Map as Map
import qualified Data.Text as Text
import Control.Monad.State hiding (state)
import qualified TxsDefs
import qualified MCRL2Defs
import qualified SortId
import qualified FuncId
import qualified ChanId
import qualified ProcId
import qualified CstrId
import qualified VarId

type T2MMonad = StateT T2MEnv IO

data T2MRegisteredObject = RegSort MCRL2Defs.ObjectId
                         | RegCstr MCRL2Defs.ObjectId MCRL2Defs.ObjectId
                         | RegVar MCRL2Defs.Variable
                         | RegMapping MCRL2Defs.ObjectId
                         | RegAction MCRL2Defs.ObjectId
                         | RegProcess MCRL2Defs.ObjectId
-- T2MRegisteredObject

data T2MEnv = T2MEnv { txsdefs :: TxsDefs.TxsDefs
                     , specification :: MCRL2Defs.Specification
                     , objectMap :: Map.Map TxsDefs.Ident T2MRegisteredObject
                     }
-- T2MEnv

modifySpec :: (MCRL2Defs.Specification -> MCRL2Defs.Specification) -> T2MMonad ()
modifySpec f = do modify $ (\env -> env { specification = f (specification env) })

registerObject :: TxsDefs.Ident -> T2MRegisteredObject -> T2MMonad ()
registerObject idt reg = do modify $ (\env -> env { objectMap = Map.insert idt reg (objectMap env) })

getRegisteredSort :: SortId.SortId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Sort)
getRegisteredSort sortId = do
    oMap <- gets objectMap
    case Map.lookup (TxsDefs.IdSort sortId) oMap of
      Just (RegSort oId) -> do
        sorts <- gets (MCRL2Defs.sorts . specification)
        case Map.lookup oId sorts of
          Just s -> do return (oId, s)
          _ -> do return (oId, MCRL2Defs.MissingSort)
      _ -> do return (Text.pack "SORT_NOT_FOUND", MCRL2Defs.MissingSort)
-- getRegisteredSort

getRegisteredCstr :: CstrId.CstrId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Constructor)
getRegisteredCstr cstrId = do
    oMap <- gets objectMap
    case Map.lookup (TxsDefs.IdCstr cstrId) oMap of
      Just (RegCstr sId cId) -> do
        sorts <- gets (MCRL2Defs.sorts . specification)
        case Map.lookup sId sorts of
          Just (MCRL2Defs.StructSort constructors) ->
            case filter (\(MCRL2Defs.Constructor { MCRL2Defs.cstrName = cstrName }) -> cstrName == cId) constructors of
              [c] -> do return (cId, c)
              _ -> do return (cId, MCRL2Defs.MissingConstructor)
          _ -> do return (Text.pack "CSTR_NOT_FOUND", MCRL2Defs.MissingConstructor)
      _ -> do return (Text.pack "CSTR_NOT_FOUND", MCRL2Defs.MissingConstructor)
-- getRegisteredCstr

getRegisteredVar :: VarId.VarId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Variable)
getRegisteredVar varId = do
    oMap <- gets objectMap
    case Map.lookup (TxsDefs.IdVar varId) oMap of
      Just (RegVar var) -> do return (MCRL2Defs.varName var, var)
      _ -> do return (Text.pack "VAR_NOT_FOUND", MCRL2Defs.MissingVariable)
-- getRegisteredVar

getRegisteredMapping :: FuncId.FuncId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Sort)
getRegisteredMapping funcId = do
    oMap <- gets objectMap
    case Map.lookup (TxsDefs.IdFunc funcId) oMap of
      Just (RegMapping oId) -> do
        mappings <- gets (MCRL2Defs.mappings . specification)
        case Map.lookup oId mappings of
          Just m -> do return (oId, m)
          _ -> do return (oId, MCRL2Defs.MissingMapping)
      _ -> do return (Text.pack "MAPPING_NOT_FOUND", MCRL2Defs.MissingMapping)
-- getRegisteredMapping

getRegisteredAction :: ChanId.ChanId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Action)
getRegisteredAction chanId = do
    oMap <- gets objectMap
    case Map.lookup (TxsDefs.IdChan chanId) oMap of
      Just (RegAction oId) -> do
        actions <- gets (MCRL2Defs.actions . specification)
        case Map.lookup oId actions of
          Just a -> do return (oId, a)
          _ -> do return (oId, MCRL2Defs.Action [])
      _ -> do return (Text.pack "ACTION_NOT_FOUND", MCRL2Defs.MissingAction)
-- getRegisteredAction

getRegisteredProcess :: ProcId.ProcId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Process)
getRegisteredProcess procId = do
    oMap <- gets objectMap
    case Map.lookup (TxsDefs.IdProc procId) oMap of
      Just (RegProcess oId) -> do
        processes <- gets (MCRL2Defs.processes . specification)
        case Map.lookup oId processes of
          Just p -> do return (oId, p)
          _ -> do return (oId, MCRL2Defs.MissingProcess)
      _ -> do return (Text.pack "PROCESS_NOT_FOUND", MCRL2Defs.MissingProcess)
-- getRegisteredProcess

getFreshName :: MCRL2Defs.ObjectId -> T2MMonad MCRL2Defs.ObjectId
getFreshName prefix = do return prefix
-- getFreshName










