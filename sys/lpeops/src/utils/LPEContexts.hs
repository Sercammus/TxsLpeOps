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
import           Ident

type LPEContext = Map.Map Ident String

getContextFromIds :: Set.Set Ident -> LPEContext
getContextFromIds = Map.fromSet (Text.unpack . name)

getAbbrevContextFromIds :: Set.Set Ident -> LPEContext
getAbbrevContextFromIds ids =
    Map.mapWithKey abbrevName (Map.fromList (zip (Set.toList ids) [1..]))
  where
    abbrevName :: Ident -> Int -> String
    abbrevName (IdSort _) i   = "sort" ++ (show i)
    abbrevName (IdCstr _) i   = "cstr" ++ (show i)
    abbrevName (IdFunc _) i   = "func" ++ (show i)
    abbrevName (IdProc _) i   = "proc" ++ (show i)
    abbrevName (IdChan _) i   = "chan" ++ (show i)
    abbrevName (IdVar _) i    = "var" ++ (show i)
    abbrevName (IdStat _) i   = "stat" ++ (show i)
    abbrevName (IdModel _) i  = "model" ++ (show i)
    abbrevName (IdPurp _) i   = "purp" ++ (show i)
    abbrevName (IdGoal _) i   = "goal" ++ (show i)
    abbrevName (IdMapper _) i = "mapper" ++ (show i)
    abbrevName (IdCnect _) i  = "cnect" ++ (show i)
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

