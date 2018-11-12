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

module LPETypes (
LPEInstance,
LPESummand(..),
LPESummands,
LPEProcInst(..),
LPEChannelOffer,
LPEChannelOffers,
LPEParamEqs,
newLPESummand,
newLPEInstance,
paramEqsLookup,
toLPEInstance,
fromLPEInstance,
getScopeProblems
) where

import qualified Control.Monad.State as MonadState
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified SortOf
import qualified TxsDefs
import qualified TxsShow
import qualified FreeVar
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
type LPESummands = Set.Set LPESummand

-- Summands can end with a recursive instantiation of the LPE or with a STOP:
data LPEProcInst = LPEStop | LPEProcInst LPEParamEqs deriving (Eq, Ord, Show)

-- Convenience type.
-- Relates a channel with communication variables over which that channel must be synchronized.
type LPEChannelOffer = (TxsDefs.ChanId, [VarId])
type LPEChannelOffers = [LPEChannelOffer]

-- Convenience type.
-- Relates a parameter with the (initial) value of that parameter
-- (in the case of a particular process instantiation).
type LPEParamEqs = Map.Map VarId TxsDefs.VExpr

paramEqsLookup :: [VarId] -> LPEParamEqs -> [TxsDefs.VExpr]
paramEqsLookup orderedParams paramEqs = map (\p -> paramEqs Map.! p) orderedParams

toLPEParamEqs :: [(VarId, TxsDefs.VExpr)] -> LPEParamEqs
toLPEParamEqs = Map.fromList

newLPESummand :: [VarId] -> LPEChannelOffers -> TxsDefs.VExpr -> [(VarId, TxsDefs.VExpr)] -> LPESummand
newLPESummand chanVarIds chanOffers guard procInstParamEqs = LPESummand chanVarIds chanOffers guard (LPEProcInst (toLPEParamEqs procInstParamEqs))

newLPEInstance :: ([TxsDefs.ChanId], [(VarId, TxsDefs.VExpr)], [LPESummand]) -> LPEInstance
newLPEInstance (chanIds, initParamEqs, summands) = (chanIds, toLPEParamEqs initParamEqs, Set.fromList summands)

-- Constructs an LPEInstance from a process expression (unless there is a problem).
-- The process expression should be the instantiation of a process that is already linear.
toLPEInstance :: TxsDefs.BExpr                          -- Process instantiation.
              -> IOC.IOC (Either [String] LPEInstance)  -- Instance (unless there are problems).
toLPEInstance procInst = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } -> let procDefs = TxsDefs.procDefs tdefs in
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _chans paramValues -> case Map.lookup procId procDefs of
            Just procDef@(TxsDefs.ProcDef chans params body) ->
              case getParamEqs params paramValues of
                Left msgs -> return (Left msgs)
                Right eqs -> case getLPESummands procId procDef body of
                               Left msgs -> return (Left msgs)
                               Right summands -> let result = (chans, eqs, Set.fromList summands) in
                                                 let scopeProblems = getScopeProblems result in
                                                   if null scopeProblems
                                                   then return (Right result)
                                                   else return (Left scopeProblems)
            Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys procDefs))
                          return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ show (Text.unpack (ProcId.name procId)) ++ "!"])
          _ -> return (Left ["Expression must be process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"])
      _ -> return (Left ["TorXakis core is not initialized!"])
-- toLPEInstance

-- Helper function.
-- Constructs one or more summands from a TXS process expression (unless there are problems):
getLPESummands :: TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> Either [String] [LPESummand]
getLPESummands expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr =
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> if choices == Set.empty -- (An 'empty choice' is equivalent to STOP.)
                                then Right [LPESummand [] [] (cstrConst (Cbool True)) LPEStop]
                                else concatEither (map (getLPESummands expectedProcId expectedProcDef) (Set.toList choices))
      TxsDefs.ActionPref TxsDefs.ActOffer { TxsDefs.offers = offers, TxsDefs.hiddenvars = hiddenvars, TxsDefs.constraint = constraint } procInst ->
          case TxsDefs.view procInst of
            TxsDefs.ProcInst procId chanIds paramValues
                | procId /= expectedProcId -> Left ["Instantiating incorrect process, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
                | chanIds /= defChanIds -> Left ["Channel mismatch in process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
                | otherwise -> case getParamEqs params paramValues of
                                 Left msgs -> Left msgs
                                 Right eqs -> case concatEither (map (getChannelOffer params) (Set.toList offers)) of
                                                Left msgs -> Left msgs
                                                Right channelOffers -> let channelVars = concatMap snd channelOffers ++ Set.toList hiddenvars in
                                                                       let constructedSummand = LPESummand channelVars channelOffers constraint (LPEProcInst eqs) in
                                                                       let scopeProblems = getSummandScopeProblems (Set.fromList params) constructedSummand in
                                                                         if null scopeProblems
                                                                         then Right [constructedSummand]
                                                                         else Left (("Invalid summand: " ++ TxsShow.fshow expr):scopeProblems ++ [""])
            _ -> Left ["Expected process instantiation, but found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
      _ -> Left ["Expected choice or channel, but found " ++ TxsShow.fshow (TxsDefs.view expr) ++ "!"]
-- getLPESummands

-- Helper method.
-- Extracts an LPEChannelOffer for each channel offer (unless there are problems):
getChannelOffer :: [VarId] -> TxsDefs.Offer -> Either [String] [LPEChannelOffer]
getChannelOffer params TxsDefs.Offer { TxsDefs.chanid = chanid, TxsDefs.chanoffers = chanoffers } =
    case concatEither (map offerToVar chanoffers) of
      Left msgs -> Left msgs
      Right offerVars -> Right [(chanid, offerVars)]
  where
    offerToVar :: TxsDefs.ChanOffer -> Either [String] [VarId]
    offerToVar (TxsDefs.Quest varId) =
        if varId `elem` params -- The channel variable should be fresh!
        then Left ["Channel variable should be fresh, found " ++ TxsShow.fshow varId ++ "!" ]
        else Right [varId]
    offerToVar chanOffer = Left ["Invalid channel format, found " ++ TxsShow.fshow chanOffer ++ "!"]
-- getChannelOffers

-- Helper function.
-- Creates parameter equations from the specified variables and expressions (unless there are problems):
getParamEqs :: [VarId] -> [TxsDefs.VExpr] -> Either [String] LPEParamEqs
getParamEqs [] [] = Right Map.empty
getParamEqs (x:_) [] = Left ["Too few expressions, " ++ Text.unpack (VarId.name x) ++ " is unassigned!"]
getParamEqs [] (x:_) = Left ["Too many expressions, found '" ++ TxsShow.fshow x ++ "'!"]
getParamEqs (x:params) (y:paramValues) =
    case getParamEqs params paramValues of
      Left msgs -> if SortOf.sortOf x /= SortOf.sortOf y
                   then Left (("Mismatching sorts, found " ++ Text.unpack (VarId.name x) ++ " and " ++ TxsShow.fshow (SortOf.sortOf y) ++ "!"):msgs)
                   else Left msgs
      Right eqs -> if SortOf.sortOf x /= SortOf.sortOf y
                   then Left ["Mismatching sorts, found " ++ Text.unpack (VarId.name x) ++ " and " ++ TxsShow.fshow (SortOf.sortOf y) ++ "!"]
                   else Right (Map.insert x y eqs)
-- getParamEqs

-- Constructs a process expression and a process definition from an LPEInstance (unless there is a problem).
-- The process expression creates an instance of the process definition.
fromLPEInstance :: LPEInstance -> String -> IOC.IOC (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef)
fromLPEInstance (chans, paramEqs, summands) procName = do
    let orderedParams = Map.keys paramEqs
    newProcUnid <- IOC.newUnid
    let newProcId = TxsDefs.ProcId { ProcId.name = Text.pack procName
                                   , ProcId.unid = newProcUnid
                                   , ProcId.procchans = map (ProcId.ChanSort . ChanId.chansorts) chans
                                   , ProcId.procvars = map VarId.varsort orderedParams
                                   , ProcId.procexit = ProcId.NoExit }
    let newProcInit = TxsDefs.procInst newProcId chans (paramEqsLookup orderedParams paramEqs)
    let newProcBody = TxsDefs.choice (Set.fromList (map (summandToBExpr newProcId orderedParams) (Set.toList summands)))
    let newProcDef = TxsDefs.ProcDef chans orderedParams newProcBody
    return (newProcInit, newProcId, newProcDef)
  where
      -- Constructs a process expression from a summand:
      summandToBExpr :: TxsDefs.ProcId -> [VarId] -> LPESummand -> TxsDefs.BExpr
      summandToBExpr lpeProcId lpeOrderedParams (LPESummand chanVars chanOffers gd inst) =
          let usedChanVars = concatMap snd chanOffers in
          let hiddenChanVars = Set.fromList chanVars Set.\\ Set.fromList usedChanVars in
          let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map offerToOffer chanOffers), TxsDefs.constraint = gd, TxsDefs.hiddenvars = hiddenChanVars } in
            case inst of
              LPEStop -> TxsDefs.actionPref actPref TxsDefs.stop
              LPEProcInst eqs -> let procInst = TxsDefs.procInst lpeProcId chans (paramEqsLookup lpeOrderedParams eqs) in
                                   TxsDefs.actionPref actPref procInst
      -- summandToBExpr
      
      -- Constructs an offer from an offer:
      offerToOffer :: LPEChannelOffer -> TxsDefs.Offer
      offerToOffer (chanId, chanVars) = TxsDefs.Offer { TxsDefs.chanid = chanId, TxsDefs.chanoffers = [TxsDefs.Quest var | var <- chanVars] }
-- fromLPEInstance

-- This method can detect certain problems with an LPE, making finding bugs in LPE operations easier:
getScopeProblems :: LPEInstance -> [String]
getScopeProblems (_chanIds, initParamEqs, summands) = concatMap (getSummandScopeProblems (Map.keysSet initParamEqs)) (Set.toList summands)

getSummandScopeProblems :: Set.Set VarId -> LPESummand -> [String]
getSummandScopeProblems scope (LPESummand channelVars _channelOffers guard procInst) =
    let newScope = Set.union scope (Set.fromList channelVars) in
      checkExpr "Guard" newScope guard ++ checkProcInst newScope procInst
    -- checkSummand
  where
    checkProcInst :: Set.Set VarId -> LPEProcInst -> [String]
    checkProcInst _ LPEStop = []
    checkProcInst scp (LPEProcInst eqs) =
        let nonExistentParameters = Map.keysSet eqs Set.\\ scope in
          map (\p -> "Process instantiation initializes non-existent parameter: " ++ Text.unpack (VarId.name p) ++ "!") (Set.toList nonExistentParameters)
          ++
          concatMap (checkExpr "Process instantiation" scp . snd) (Map.toList eqs)
    -- checkProcInst
    
    checkExpr :: String -> Set.Set VarId -> TxsDefs.VExpr -> [String]
    checkExpr description scp expr =
        let outOfScope = Set.fromList (FreeVar.freeVars expr) Set.\\ scp in
          map (\v -> description ++ " uses out-of-scope variable: " ++ Text.unpack (VarId.name v) ++ "!") (Set.toList outOfScope)
    -- checkExpr
-- getSummandScopeProblems


