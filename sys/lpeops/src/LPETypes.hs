{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPETypes
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module LPETypes (
LPEInstance,
LPESummand(..),
LPESummands,
LPEProcInst(..),
LPEChannelOffer,
LPEChannelOffers,
LPEParamEq,
LPEParamEqs,
extractVExprFromMap,
extractVExprFromParamEqs,
toLPEInstance,
fromLPEInstance
) where

import           Control.Monad.State
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified EnvData
import qualified SortOf
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import           VarId
import           ChanId
import           Name
import           Constant
import           ValExpr

-- Type around which this module revolves.
-- It consists of the following parts:
--  - Channels used by the LPE.
--  - Parameters used by the LPE and their initial values, coupled in pairs.
--  - Contents of each summand of the LPE.
type LPEInstance = ([TxsDefs.ChanId], LPEParamEqs, LPESummands)

-- Main building block of an LPE.
-- Each summand provides the following pieces of critical information:
--  - Channel offers (channel references and fresh variables for communication over those channel).
--  - Guard (capable of restricting the value of the communication variable).
--  - Possibly a number of value initializations (for the instantiation of the next process).
data LPESummand = LPESummand LPEChannelOffers TxsDefs.VExpr LPEProcInst deriving (Eq, Ord, Show)
type LPESummands = [LPESummand]

-- Summands can have a process instantiation or STOP:
data LPEProcInst = LPEStop | LPEProcInst LPEParamEqs deriving (Eq, Ord, Show)

-- Convenience type.
-- Relates a channel with communication variables over which that channel must be synchronized.
type LPEChannelOffer = (TxsDefs.ChanId, [VarId])
type LPEChannelOffers = [LPEChannelOffer]

-- Convenience type.
-- Relates a parameter with the (initial) value of that parameter
-- (in the case of a particular process instantiation).
type LPEParamEq = (VarId, TxsDefs.VExpr)
type LPEParamEqs = [LPEParamEq]

-- Extracts the data expression that corresponds with the specified variable from a map.
-- The variable should be in the specified map (unchecked precondition)!
extractVExprFromMap :: VarId -> Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr
extractVExprFromMap varId m = Map.findWithDefault (cstrConst (Cany (SortOf.sortOf varId))) varId m

-- Extracts the data expression that corresponds with the specified variable from a number of parameter equations.
-- One of the equations should have the specified variable on the left-hand side (precondition)!
extractVExprFromParamEqs :: VarId -> LPEParamEqs -> TxsDefs.VExpr
extractVExprFromParamEqs varId paramEqs = extractVExprFromMap varId (Map.fromList paramEqs)

-- Helper function.
-- Checks if the types of the specified variables and values match.
typeCheckParams :: [VarId] -> [TxsDefs.VExpr] -> Bool
typeCheckParams [] [] = True
typeCheckParams _ [] = False
typeCheckParams [] _ = False
typeCheckParams (x:params) (y:paramValues) = ((SortOf.sortOf x) == (SortOf.sortOf y)) && (typeCheckParams params paramValues)

-- -- Helper function.
-- -- Folds a number of objects, unless one of them equals Nothing:
-- foldMaybes :: Foldable t => (b -> a -> Maybe b) -> b -> t a -> Maybe b
-- foldMaybes f x y = foldl f' (Just x) y
  -- where
    -- f' (Just x') y' = f x' y'
    -- f' _ _ = Nothing
-- -- foldMaybes

-- Helper function.
-- Maps a number of objects, unless for one of them the mapping yields Nothing:
mapMaybesM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe [b])
mapMaybesM f x = Monad.foldM f' (Just []) x
  where
    f' (Just soFar) x' = do x'' <- f x'
                            case x'' of
                              Just x''' -> do return (Just (soFar ++ [x''']))
                              Nothing -> do return Nothing
    f' _ _ = do return Nothing
-- mapMaybesM

concatMaybesM :: Monad m => m (Maybe [[t]]) -> m (Maybe [t])
concatMaybesM x = do x' <- x
                     case x' of
                       Just x'' -> do return (Just (concat x''))
                       Nothing -> do return Nothing
-- concatMaybesM

-- Exposed function.
-- Constructs an LPEInstance from a process expression (unless there is a problem).
-- The process expression should be the instantiation of a process that is already linear.
toLPEInstance :: TxsDefs.BExpr                 -- Process instantiation.
               -> IOC.IOC (Maybe LPEInstance)  -- Instance (unless there is a problem).
toLPEInstance procInst = do
    envc <- get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } -> let procDefs = TxsDefs.procDefs tdefs in
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _chans paramValues -> case Map.lookup procId procDefs of
            Just procDef@(TxsDefs.ProcDef chans params body) -> if typeCheckParams params paramValues
                                                                then do maybeSummands <- getLPESummands procId procDef body
                                                                        return (case maybeSummands of
                                                                          Just summands -> Just (chans, zip params paramValues, Set.toList (Set.fromList summands))
                                                                          Nothing -> Nothing)
                                                                else do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: parameter mismatch " ++ (show procId)) ]
                                                                        return Nothing
            _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: undefined process " ++ (show procId)) ]
                    return Nothing
          _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: expression must be process instantiation, found " ++ (TxsShow.fshow (TxsDefs.view procInst))) ]
                  return Nothing
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "toLPEInstance: only allowed if initialized" ]
              return Nothing
-- toLPEInstance

-- Helper function.
-- Constructs one or more summands from a TXS process expression (unless there is a problem).
getLPESummands :: TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> IOC.IOC (Maybe LPESummands)
getLPESummands expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr = do
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> if choices == Set.empty -- (An 'empty choice' is equivalent to STOP.)
                                then do return (Just [LPESummand [] (cstrConst (Cbool True)) LPEStop])
                                else concatMaybesM (mapMaybesM (getLPESummands expectedProcId expectedProcDef) (Set.toList choices))
      TxsDefs.ActionPref (TxsDefs.ActOffer { TxsDefs.offers = offers, TxsDefs.constraint = constraint }) procInst ->
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId chanIds paramValues ->
            if (procId == expectedProcId) && (chanIds == defChanIds) && (typeCheckParams params paramValues)
            then do maybeChannelOffers <- mapMaybesM (getChannelOffer params) (Set.toList offers)
                    case maybeChannelOffers of
                      Just channelOffers -> do return (Just [LPESummand channelOffers constraint (LPEProcInst (zip params paramValues))])
                      Nothing -> do return Nothing
            else do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: mismatching instantiation in " ++ (TxsShow.fshow (TxsDefs.view procInst))) ]
                    return Nothing
          _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: expected ProcInst, but found " ++ (TxsShow.fshow (TxsDefs.view procInst))) ]
                  return Nothing
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: expected Choice or ActionPref, but found " ++ (TxsShow.fshow (TxsDefs.view expr))) ]
              return Nothing
-- getLPESummands

-- Helper method.
-- Extracts an LPEChannelOffer for each channel offer (unless there is a problem).
getChannelOffer :: [VarId] -> TxsDefs.Offer -> IOC.IOC (Maybe LPEChannelOffer)
getChannelOffer params (TxsDefs.Offer { TxsDefs.chanid = chanid, TxsDefs.chanoffers = chanoffers }) = do
    offers <- mapMaybesM mapOffer chanoffers
    case offers of
      Just offerVars -> do return (Just (chanid, offerVars))
      Nothing -> do return Nothing
  where
    mapOffer :: TxsDefs.ChanOffer -> IOC.IOC (Maybe VarId)
    mapOffer (TxsDefs.Quest varId) =
        if varId `elem` params -- The channel variable should be fresh!
        then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: channel variable should be fresh, found " ++ (TxsShow.fshow varId)) ]
                return Nothing
        else do return (Just varId)
    mapOffer chanOffer = do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: invalid channel format, found " ++ (TxsShow.fshow chanOffer)) ]
                            return Nothing
-- getChannelOffers

-- Exposed method.
-- Constructs a process expression and a process definition from an LPEInstance (unless there is a problem).
-- The process expression creates an instance of the process definition.
fromLPEInstance :: LPEInstance -> Name -> IOC.IOC (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef)
fromLPEInstance (chans, paramEqs, summands) procName = do
    let newProcParams = map fst paramEqs
    newProcUnid <- IOC.newUnid
    let newProcId = TxsDefs.ProcId { ProcId.name = Text.pack (Text.unpack procName)
                                   , ProcId.unid = newProcUnid
                                   , ProcId.procchans = map (ProcId.ChanSort . ChanId.chansorts) chans
                                   , ProcId.procvars = map (VarId.varsort) newProcParams
                                   , ProcId.procexit = ProcId.NoExit }
    let newProcInit = TxsDefs.procInst newProcId chans (map snd paramEqs)
    let newProcDef = TxsDefs.ProcDef chans newProcParams (TxsDefs.choice (Set.fromList (summandIterator summands newProcId)))
    return (newProcInit, newProcId, newProcDef)
  where
      -- Constructs a process expression from a summand:
      summandIterator :: [LPESummand] -> TxsDefs.ProcId -> [TxsDefs.BExpr]
      summandIterator [] _ = []
      summandIterator (summand:xs) lpeProcId =
          case summand of
            LPESummand channelOffers gd LPEStop -> let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map fromOfferToOffer channelOffers), TxsDefs.constraint = gd, TxsDefs.hiddenvars = Set.empty } in
                (TxsDefs.actionPref actPref TxsDefs.stop):(summandIterator xs lpeProcId)
            LPESummand channelOffers gd (LPEProcInst eqs) -> let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map fromOfferToOffer channelOffers), TxsDefs.constraint = gd, TxsDefs.hiddenvars = Set.empty } in
              let procInst = TxsDefs.procInst lpeProcId chans (map snd eqs) in
                (TxsDefs.actionPref actPref procInst):(summandIterator xs lpeProcId)
      
      -- Constructs an offer from an offer:
      fromOfferToOffer :: LPEChannelOffer -> TxsDefs.Offer
      fromOfferToOffer (chanId, chanVars) = TxsDefs.Offer { TxsDefs.chanid = chanId, TxsDefs.chanoffers = [TxsDefs.Quest var | var <- chanVars] }
-- fromLPEInstance






