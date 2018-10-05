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
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified SortOf
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import           VarId
import           ChanId
import           Constant
import           ValExpr
import           ConcatEither

-- Type around which this module revolves.
-- It consists of the following parts:
--  - Channels used by the LPE (included mostly so that conversion to TXS is possible without additional channel information).
--  - Parameters used by the LPE and their initial values (each pair forms a 'parameter equation').
--  - List of summands of the LPE.
type LPEInstance = ([TxsDefs.ChanId], LPEParamEqs, LPESummands)

-- Main building block of an LPE.
-- Each summand provides the following pieces of critical information:
--  - All channel variables, including hidden variables.
--  - Channel offers (action prefices and the *fresh* variables - also found in the earlier list - used per action prefix for synchronization).
--  - Guard (restriction on when the summand can be 'applied').
--  - STOP, or a number of parameter equations to be used for the recursive instantiation.
data LPESummand = LPESummand [VarId] LPEChannelOffers TxsDefs.VExpr LPEProcInst deriving (Eq, Ord, Show)
type LPESummands = [LPESummand]

-- Summands can end with a recursive instantiation of the LPE or with a STOP:
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
-- The variable should be in the specified map (unchecked precondition!);
-- however, if the variable is not found the function returns ANY <variable sort>.
extractVExprFromMap :: VarId -> Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr
extractVExprFromMap varId m = Map.findWithDefault (cstrConst (Cany (SortOf.sortOf varId))) varId m

-- Extracts the data expression that corresponds with the specified parameter from a number of parameter equations.
-- One of the equations should have the specified parameter on the left-hand side;
-- however, if the parameter is not found the function returns ANY <parameter sort>.
extractVExprFromParamEqs :: VarId -> LPEParamEqs -> TxsDefs.VExpr
extractVExprFromParamEqs varId paramEqs = extractVExprFromMap varId (Map.fromList paramEqs)

-- Exposed function.
-- Constructs an LPEInstance from a process expression (unless there is a problem).
-- The process expression should be the instantiation of a process that is already linear.
toLPEInstance :: TxsDefs.BExpr                          -- Process instantiation.
              -> IOC.IOC (Either [String] LPEInstance)  -- Instance (unless there are problems).
toLPEInstance procInst = do
    envc <- get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } -> let procDefs = TxsDefs.procDefs tdefs in
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _chans paramValues -> case Map.lookup procId procDefs of
            Just procDef@(TxsDefs.ProcDef chans params body) ->
              case getParamEqs params paramValues of
                Left msgs -> do return (Left msgs)
                Right eqs -> case getLPESummands procId procDef body of
                               Left msgs -> do return (Left msgs)
                               Right summands -> do return (Right (chans, eqs, summands))
            Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys procDefs))
                          return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ (show (Text.unpack (ProcId.name procId))) ++ "!"])
          _ -> do return (Left ["Expression must be process instantiation, found " ++ (TxsShow.fshow (TxsDefs.view procInst)) ++ "!"])
      _ -> do return (Left ["TorXakis core is not initialized!"])
-- toLPEInstance

-- Helper function.
-- Constructs one or more summands from a TXS process expression (unless there are problems):
getLPESummands :: TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> Either [String] [LPESummand]
getLPESummands expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr =
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> if choices == Set.empty -- (An 'empty choice' is equivalent to STOP.)
                                then Right [LPESummand [] [] (cstrConst (Cbool True)) LPEStop]
                                else concatEither (map (getLPESummands expectedProcId expectedProcDef) (Set.toList choices))
      TxsDefs.ActionPref (TxsDefs.ActOffer { TxsDefs.offers = offers, TxsDefs.hiddenvars = hiddenvars, TxsDefs.constraint = constraint }) procInst ->
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId chanIds paramValues ->
            if procId /= expectedProcId
            then Left ["Instantiating incorrect process, found " ++ (TxsShow.fshow (TxsDefs.view procInst)) ++ "!"]
            else if chanIds /= defChanIds
                 then Left ["Channel mismatch in process instantiation, found " ++ (TxsShow.fshow (TxsDefs.view procInst)) ++ "!"]
                 else case getParamEqs params paramValues of
                        Left msgs -> Left msgs
                        Right eqs -> case concatEither (map (getChannelOffer params) (Set.toList offers)) of
                                       Left msgs -> Left msgs
                                       Right channelOffers -> let channelVars = (concat (map snd channelOffers)) ++ (Set.toList hiddenvars) in
                                                                Right [LPESummand channelVars channelOffers constraint (LPEProcInst eqs)]
          _ -> Left ["Expected process instantiation, but found " ++ (TxsShow.fshow (TxsDefs.view procInst)) ++ "!"]
      _ -> Left ["Expected choice or channel, but found " ++ (TxsShow.fshow (TxsDefs.view expr)) ++ "!"]
-- getLPESummands

-- Helper method.
-- Extracts an LPEChannelOffer for each channel offer (unless there are problems):
getChannelOffer :: [VarId] -> TxsDefs.Offer -> Either [String] [LPEChannelOffer]
getChannelOffer params (TxsDefs.Offer { TxsDefs.chanid = chanid, TxsDefs.chanoffers = chanoffers }) =
    case concatEither (map offerToVar chanoffers) of
      Left msgs -> Left msgs
      Right offerVars -> Right [(chanid, offerVars)]
  where
    offerToVar :: TxsDefs.ChanOffer -> Either [String] [VarId]
    offerToVar (TxsDefs.Quest varId) =
        if varId `elem` params -- The channel variable should be fresh!
        then do Left ["Channel variable should be fresh, found " ++ (TxsShow.fshow varId) ++ "!" ]
        else do Right [varId]
    offerToVar chanOffer = Left ["Invalid channel format, found " ++ (TxsShow.fshow chanOffer) ++ "!"]
-- getChannelOffers

-- Helper function.
-- Creates parameter equations from the specified variables and expressions (unless there are problems):
getParamEqs :: [VarId] -> [TxsDefs.VExpr] -> Either [String] [LPEParamEq]
getParamEqs [] [] = Right []
getParamEqs (x:_) [] = Left ["Too few expressions, " ++ (Text.unpack (VarId.name x)) ++ " is unassigned!"]
getParamEqs [] (x:_) = Left ["Too many expressions, found '" ++ (TxsShow.fshow x) ++ "'!"]
getParamEqs (x:params) (y:paramValues) =
    case getParamEqs params paramValues of
      Left msgs -> if (SortOf.sortOf x) /= (SortOf.sortOf y)
                   then Left (("Mismatching sorts, found " ++ (Text.unpack (VarId.name x)) ++ " and " ++ (TxsShow.fshow y) ++ "!"):msgs)
                   else Left msgs
      Right eqs -> if (SortOf.sortOf x) /= (SortOf.sortOf y)
                   then Left ["Mismatching sorts, found " ++ (Text.unpack (VarId.name x)) ++ " and " ++ (TxsShow.fshow y) ++ "!"]
                   else Right ((x, y):eqs)
-- getParamEqs

-- Exposed method.
-- Constructs a process expression and a process definition from an LPEInstance (unless there is a problem).
-- The process expression creates an instance of the process definition.
fromLPEInstance :: LPEInstance -> String -> IOC.IOC (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef)
fromLPEInstance (chans, paramEqs, summands) procName = do
    let newProcParams = map fst paramEqs
    newProcUnid <- IOC.newUnid
    let newProcId = TxsDefs.ProcId { ProcId.name = (Text.pack procName)
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
            LPESummand chanVars chanOffers gd inst -> let usedChanVars = concat (map snd chanOffers) in
                                                      let hiddenChanVars = (Set.fromList chanVars) Set.\\ (Set.fromList usedChanVars) in
                                                      let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map fromOfferToOffer chanOffers), TxsDefs.constraint = gd, TxsDefs.hiddenvars = hiddenChanVars } in
                                                        case inst of
                                                          LPEStop -> (TxsDefs.actionPref actPref TxsDefs.stop):(summandIterator xs lpeProcId)
                                                          LPEProcInst eqs -> let procInst = TxsDefs.procInst lpeProcId chans (map snd eqs) in
                                                                               (TxsDefs.actionPref actPref procInst):(summandIterator xs lpeProcId)
      -- summandIterator
      
      -- Constructs an offer from an offer:
      fromOfferToOffer :: LPEChannelOffer -> TxsDefs.Offer
      fromOfferToOffer (chanId, chanVars) = TxsDefs.Offer { TxsDefs.chanid = chanId, TxsDefs.chanoffers = [TxsDefs.Quest var | var <- chanVars] }
-- fromLPEInstance


