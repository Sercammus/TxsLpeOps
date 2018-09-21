{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ValFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module ValFactory (
sort2defaultValue
) where

import qualified Control.Monad as Monad
import           Control.Monad.State hiding (state)
import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified EnvData
import qualified TxsDefs
import qualified ValExpr
import qualified SortId
import qualified Constant
import qualified CstrId

sort2defaultValue :: SortId.SortId -> IOC.IOC TxsDefs.VExpr
sort2defaultValue sortId =
    if sortId == SortId.sortIdBool then do return (ValExpr.cstrConst (Constant.Cbool False)) else
    if sortId == SortId.sortIdInt then do return (ValExpr.cstrConst (Constant.Cint 0)) else
    if sortId == SortId.sortIdString then do return (ValExpr.cstrConst (Constant.Cstring (Text.pack ""))) else
    if sortId == SortId.sortIdRegex then do return (ValExpr.cstrConst (Constant.Cstring (Text.pack ""))) else
      do
        cstrDefs <- gets (TxsDefs.cstrDefs . IOC.tdefs . IOC.state)
        case [ cstrId | cstrId <- Map.keys cstrDefs, (CstrId.cstrsort cstrId) == sortId ] of
          [cstrId] -> do generatedArgs <- Monad.mapM sort2defaultValue (CstrId.cstrargs cstrId)
                         return (ValExpr.cstrCstr cstrId generatedArgs)
          _ -> do IOC.putMsgs [ EnvData.TXS_CORE_SYSTEM_ERROR ("Failed to generate a default value for " ++ (show sortId)) ]
                  return (ValExpr.cstrConst (Constant.Cany sortId))
-- sort2defaultValue

