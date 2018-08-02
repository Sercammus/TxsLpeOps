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
LPEChannelOffer,
LPEChannelOffers,
LPEParamEq,
LPEParamEqs,
toLPEInstance,
fromLPEInstance
) where

import           Control.Monad.State
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import           VarId
import           Name
import qualified ProcId

-- Type around which this module revolves.
-- It consists of the following parts:
--  - Parameters the LPE and their initial values, coupled in pairs;
--  - Information per summand of the LPE.
type LPEInstance = ([TxsDefs.ChanId], LPEParamEqs, LPESummands)

-- Convenience type.
-- Each summand provides the following pieces of critical information:
--  - Guard (capable of restricting the value of the communication variable).
--  - A number of value initializations (for the instantiation of the next process).
data LPESummand = LPEStopSummand | LPESummand LPEChannelOffers TxsDefs.VExpr LPEParamEqs
type LPESummands = [LPESummand]

-- Convenience type.
-- Relates a channel with communication variables over which that channel must be synchronized.
type LPEChannelOffer = (TxsDefs.ChanId, [VarId])
type LPEChannelOffers = [LPEChannelOffer]

-- Convenience type.
-- Relates a parameter with the (initial) value of that parameter
-- (in the case of a particular process instantiation).
type LPEParamEq = (VarId, TxsDefs.VExpr)
type LPEParamEqs = [LPEParamEq]

-- Exposed method.
-- Constructs an LPEInstance from a process expression (unless there is a problem).
-- The process expression should be the instantiation of a process that is already linear.
toLPEInstance :: TxsDefs.BExpr                 -- Process instantiation; must be a closed expression!
               -> IOC.IOC (Maybe LPEInstance)  -- Instance.
toLPEInstance procInst = do
    envc <- get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } -> let procDefs = TxsDefs.procDefs tdefs in
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _chans paramValues -> case Map.lookup procId procDefs of
            Just procDef@(TxsDefs.ProcDef chans params _) -> do maybeSummands <- getLPESummands procId procDef
                                                                return (case maybeSummands of
                                                                  Just summands -> Just (chans, zip params paramValues, summands)
                                                                  _ -> Nothing)
            _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: undefined process definition " ++ (show procId)) ]
                    return Nothing
          _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("toLPEInstance: only defined for process instantiation, found " ++ (TxsShow.fshow (TxsDefs.view procInst))) ]
                  return Nothing
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "toLPEInstance: only allowed if initialized" ]
              return Nothing
-- toLPEInstance

-- Helper method.
-- Constructs an LPESummand for each summand in an LPE process.
getLPESummands :: TxsDefs.ProcId               -- Id of the linear process (summands may only instantiate this process).
               -> TxsDefs.ProcDef              -- Definition of the linear process (body is analyzed).
               -> IOC.IOC (Maybe LPESummands)  -- List of summands (unless there is a problem).
getLPESummands expectedProcId expectedProcDef@(TxsDefs.ProcDef _ _ (TxsDefs.view -> TxsDefs.Choice summands)) = getLPESummandIterator expectedProcId expectedProcDef summands
getLPESummands expectedProcId expectedProcDef@(TxsDefs.ProcDef _ _ summand) = getLPESummandIterator expectedProcId expectedProcDef [summand]

-- Helper method.
-- Constructs LPESummands from a number of process expressions.
getLPESummandIterator :: TxsDefs.ProcId               -- Id of the linear process (summands may only instantiate this process).
                      -> TxsDefs.ProcDef              -- Definition of the linear process (allows instantiation parameters to be checked).
                      -> [TxsDefs.BExpr]              -- List of expressions that must correspond with summands.
                      -> IOC.IOC (Maybe LPESummands)  -- List of summands (unless there is a problem).
getLPESummandIterator _ _ [] = do return (Just [])
getLPESummandIterator expectedProcId expectedProcDef@(TxsDefs.ProcDef _ params _) (summand:xs) = do
    -- Only two types of summands are valid, stop summands and linear summands:
    case TxsDefs.view summand of
      TxsDefs.Stop -> do maybeOtherSummands <- getLPESummandIterator expectedProcId expectedProcDef xs
                         return (case maybeOtherSummands of
                           Just otherSummands -> Just (LPEStopSummand:otherSummands)
                           _ -> Nothing)
      TxsDefs.ActionPref (TxsDefs.ActOffer { TxsDefs.offers = offers, TxsDefs.constraint = constraint }) procInst -> case TxsDefs.view procInst of
        TxsDefs.ProcInst procId _chans paramValues -> if (procId == expectedProcId) && (True) -- TODO check types of param values, channels!
                                                      then do maybeChannelOffers <- getChannelOffers (Set.toList offers)
                                                              case maybeChannelOffers of
                                                                Just channelOffers -> do maybeOtherSummands <- getLPESummandIterator expectedProcId expectedProcDef xs
                                                                                         return (case maybeOtherSummands of
                                                                                           Just otherSummands -> Just ((LPESummand channelOffers constraint (zip params paramValues)):otherSummands)
                                                                                           _ -> Nothing)
                                                                _ -> do return Nothing
                                                      else do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("getLPESummandIterator: invalid LPE instantiation, found " ++ (TxsShow.fshow (TxsDefs.view procInst))) ]
                                                              return Nothing
        _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("getLPESummandIterator: invalid LPE instantiation, found " ++ (TxsShow.fshow (TxsDefs.view procInst))) ]
                return Nothing
      _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("getLPESummandIterator: invalid summand format, found " ++ (TxsShow.fshow (TxsDefs.view summand))) ]
              return Nothing
-- getLPESummandIterator

-- Helper method.
-- Extracts an LPEChannelOffer for each channel offer (unless there is a problem).
getChannelOffers :: [TxsDefs.Offer] -> IOC.IOC (Maybe LPEChannelOffers)
getChannelOffers [] = do return (Just [])
getChannelOffers (TxsDefs.Offer { TxsDefs.chanid = chanid, TxsDefs.chanoffers = chanoffers }:xs) = do
    maybeOfferVariables <- getOfferVariables chanoffers
    case maybeOfferVariables of
      Just vars -> do maybeOtherOffers <- getChannelOffers xs
                      return (case maybeOtherOffers of
                        Just otherOffers -> Just ((chanid, vars):otherOffers)
                        _ -> Nothing)
      _ -> return Nothing
    where
      getOfferVariables :: [TxsDefs.ChanOffer] -> IOC.IOC (Maybe [VarId])
      getOfferVariables [] = return (Just [])
      getOfferVariables (v:vs) = case v of
          TxsDefs.Quest var -> do maybeOtherVars <- getOfferVariables vs
                                  return (case maybeOtherVars of
                                    Just otherVars -> Just (var:otherVars)
                                    _ -> Nothing)
          _ -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("getOfferVariables: invalid channel offer variable found, found " ++ (TxsShow.fshow v)) ]
                  return Nothing
-- getChannelOffers

-- Exposed method.
-- Constructs a process expression and a process definition from an LPEInstance (unless there is a problem).
-- The process expression creates an instance of the process definition.
fromLPEInstance :: LPEInstance -> Name -> IOC.IOC (TxsDefs.BExpr, TxsDefs.ProcDef)
fromLPEInstance (chans, paramEqs, summands) procName = do
    let newProcParams = map fst paramEqs
    newProcUnid <- IOC.newUnid
    let newProcId = TxsDefs.ProcId { ProcId.name = Text.pack ((Text.unpack procName) ++ "$" ++ (show newProcUnid))
                                   , ProcId.unid = newProcUnid
                                   , ProcId.procchans = chans
                                   , ProcId.procvars = newProcParams
                                   , ProcId.procexit = ProcId.NoExit }
    let newProcInit = TxsDefs.procInst newProcId chans (map snd paramEqs)
    let newProcDef = TxsDefs.ProcDef chans newProcParams (TxsDefs.choice (summandIterator summands newProcId))
    return (newProcInit, newProcDef)
    where
      -- Constructs a process expression from a summand:
      summandIterator :: [LPESummand] -> TxsDefs.ProcId -> [TxsDefs.BExpr]
      summandIterator [] _ = []
      summandIterator (summand:xs) lpeProcId =
          case summand of
            LPEStopSummand -> (TxsDefs.stop):(summandIterator xs lpeProcId)
            LPESummand channelOffers gd eqs -> let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map fromOfferToOffer channelOffers), TxsDefs.constraint = gd } in
              let procInst = TxsDefs.procInst lpeProcId chans (map snd eqs) in
                (TxsDefs.actionPref actPref procInst):(summandIterator xs lpeProcId)
      
      -- Constructs an offer from an offer:
      fromOfferToOffer :: LPEChannelOffer -> TxsDefs.Offer
      fromOfferToOffer (chanId, chanVars) = TxsDefs.Offer { TxsDefs.chanid = chanId, TxsDefs.chanoffers = [TxsDefs.Quest var | var <- chanVars] }
-- fromLPEInstance






