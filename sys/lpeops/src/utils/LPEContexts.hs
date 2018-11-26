{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEContexts
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEContexts (
LPEContext,
getContextFromIds,
getAbbrevContextFromIds,
getModelContext,
getProcessContext,
getSummandContext,
getValExprContext,
getAbbrevModelContext,
getAbbrevProcessContext,
getAbbrevSummandContext,
getAbbrevValExprContext
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import           LPETypeDefs
import           LPEContextIds

type LPEContext = Map.Map TxsDefs.Ident String

getContextFromIds :: Set.Set TxsDefs.Ident -> LPEContext
getContextFromIds = Map.fromSet (Text.unpack . TxsDefs.name)

getAbbrevContextFromIds :: Set.Set TxsDefs.Ident -> LPEContext
getAbbrevContextFromIds ids =
    Map.mapWithKey abbrevName (Map.fromList (zip (Set.toList ids) [1..]))
  where
    abbrevName :: TxsDefs.Ident -> Int -> String
    abbrevName (TxsDefs.IdSort _) i   = "sort" ++ (show i)
    abbrevName (TxsDefs.IdCstr _) i   = "cstr" ++ (show i)
    abbrevName (TxsDefs.IdFunc _) i   = "func" ++ (show i)
    abbrevName (TxsDefs.IdProc _) i   = "proc" ++ (show i)
    abbrevName (TxsDefs.IdChan _) i   = "chan" ++ (show i)
    abbrevName (TxsDefs.IdVar _) i    = "var" ++ (show i)
    abbrevName (TxsDefs.IdStat _) i   = "stat" ++ (show i)
    abbrevName (TxsDefs.IdModel _) i  = "model" ++ (show i)
    abbrevName (TxsDefs.IdPurp _) i   = "purp" ++ (show i)
    abbrevName (TxsDefs.IdGoal _) i   = "goal" ++ (show i)
    abbrevName (TxsDefs.IdMapper _) i = "mapper" ++ (show i)
    abbrevName (TxsDefs.IdCnect _) i  = "cnect" ++ (show i)
-- getAbbrevContextFromIds

getModelContext :: LPEModel -> LPEContext
getModelContext = getContextFromIds . getModelIds

getProcessContext :: LPEProcess -> LPEContext
getProcessContext = getContextFromIds . getProcessIds

getSummandContext :: LPESummand -> LPEContext
getSummandContext = getContextFromIds . getSummandIds

getValExprContext :: TxsDefs.VExpr -> LPEContext
getValExprContext = getContextFromIds . getValExprIds

getAbbrevModelContext :: LPEModel -> LPEContext
getAbbrevModelContext = getAbbrevContextFromIds . getModelIds

getAbbrevProcessContext :: LPEProcess -> LPEContext
getAbbrevProcessContext = getAbbrevContextFromIds . getProcessIds

getAbbrevSummandContext :: LPESummand -> LPEContext
getAbbrevSummandContext = getAbbrevContextFromIds . getSummandIds

getAbbrevValExprContext :: TxsDefs.VExpr -> LPEContext
getAbbrevValExprContext = getAbbrevContextFromIds . getValExprIds
