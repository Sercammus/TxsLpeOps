{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Satisfiability
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module VarFactory (
createFreshVar,
createFreshVarFromPrefix
) where

import qualified EnvCore as IOC
import qualified Data.Text as Text
import qualified SortId
import qualified Id
import VarId

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVar :: SortId.SortId -> IOC.IOC VarId.VarId
createFreshVar sort = do
    varUnid <- IOC.newUnid
    let idAsInt = Id._id varUnid
    let absId = if idAsInt >= 0 then idAsInt else -idAsInt
    return VarId.VarId { VarId.name = Text.pack ("__FV" ++ (show absId)), VarId.unid = varUnid, VarId.varsort = sort }
-- createVar

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVarFromPrefix :: String -> SortId.SortId -> IOC.IOC VarId.VarId
createFreshVarFromPrefix prefix sort = do
    varUnid <- IOC.newUnid
    let idAsInt = Id._id varUnid
    let absId = if idAsInt >= 0 then idAsInt else -idAsInt
    return VarId.VarId { VarId.name = Text.pack (prefix ++ (show absId)), VarId.unid = varUnid, VarId.varsort = sort }
-- createFreshVarFromPrefix


