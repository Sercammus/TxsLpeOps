{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ModelIdFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ModelIdFactory (
getModelsByName,
getModelIdFromName
) where

import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified ModelId
import qualified TxsDefs

getModelsByName :: String -> IOC.IOC (Map.Map ModelId.ModelId TxsDefs.ModelDef)
getModelsByName modelName = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        return (Map.filterWithKey (\(TxsDefs.ModelId n _) _ -> Text.unpack n == modelName) (TxsDefs.modelDefs tdefs))
      _ -> return Map.empty
-- getModelsByName

getModelIdFromName :: String -> IOC.IOC ModelId.ModelId
getModelIdFromName modelName = do
    matchingModels <- getModelsByName modelName
    case Map.toList matchingModels of
      [] -> do TxsDefs.ModelId (Text.pack modelName) <$> IOC.newUnid
      (mid, _):_ -> return mid
-- getModelIdFromName

