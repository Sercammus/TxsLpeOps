{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TXS2MCRL2
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns #-}
module TXS2MCRL2 (
txs2mcrl2
) where

import TXS2MCRL2Env
import Control.Monad.State hiding (guard, state)
import qualified Control.Monad as Monad
import qualified Data.Char as Char
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified FreeMonoidX as FMX
import qualified TxsDefs
import qualified MCRL2Defs
import qualified SortId
import qualified SortDef
import qualified FuncId
import qualified FuncDef
import qualified VarId
import qualified ValExpr
import qualified ProcId
import qualified ModelId
import qualified ChanId
import qualified CstrId
import qualified CstrDef
import qualified ConstDefs

txs2mcrl2 :: TxsDefs.TxsDefs -> T2MMonad ()
txs2mcrl2 tdefs = do
    -- Initialize the state data:
    modify $ (\env -> env { specification = MCRL2Defs.emptySpecification, txsdefs = tdefs })
    -- Translate sorts.
    -- These contain no information, because they are defined further via constructors:
    sorts <- Monad.mapM sortDef2sortDef (Map.toList (TxsDefs.sortDefs tdefs))
    modifySpec $ (\spec -> spec { MCRL2Defs.sorts = Map.fromList sorts })
    -- Translate constructors:
    Monad.mapM_ constructor2constructor (Map.toList (TxsDefs.cstrDefs tdefs))
    -- Translate function headers to mappings:
    mappings <- Monad.mapM function2mapping (Map.toList (TxsDefs.funcDefs tdefs))
    modifySpec $ (\spec -> spec { MCRL2Defs.mappings = Map.fromList mappings })
    -- Translate function bodies to equation groups:
    eqGroups <- Monad.mapM function2eqGroup (Map.toList (TxsDefs.funcDefs tdefs))
    modifySpec $ (\spec -> spec { MCRL2Defs.equationGroups = eqGroups })
    -- Translate channels:
    Monad.mapM_ process2actions (Map.toList (TxsDefs.procDefs tdefs))
    Monad.mapM_ model2actions (Map.toList (TxsDefs.modelDefs tdefs))
    -- Translate processes while ignoring bodies:
    processes <- Monad.mapM process2processHeader (Map.toList (TxsDefs.procDefs tdefs))
    modifySpec $ (\spec -> spec { MCRL2Defs.processes = Map.fromList processes })
    -- Translate the bodies of processes:
    Monad.mapM_ process2processBody (Map.toList (TxsDefs.procDefs tdefs))
-- txs2mcrl2

-- Creates an mCRL2 sort declaration from a TXS sort declaration:
sortDef2sortDef :: (SortId.SortId, SortDef.SortDef) -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Sort)
sortDef2sortDef (sortId, _) = do
    sortName <- getFreshName (SortId.name sortId)
    registerObject (TxsDefs.IdSort sortId) (RegSort sortName)
    return $ (sortName, MCRL2Defs.ImplicitSort) -- SortDefs do not contain information (they are defined via constructors).
-- sortDef2sortDef

-- Creates an mCRL2 constructor from a TXS constructor:
constructor2constructor :: (CstrId.CstrId, CstrDef.CstrDef) -> T2MMonad ()
constructor2constructor (cstrId, CstrDef.CstrDef recognizer projections) = do
    -- Create the mCRL2 constructor:
    constructorName <- getFreshName (CstrId.name cstrId)
    recognizerName <- getFreshName (FuncId.name recognizer)
    projectionNames <- Monad.mapM (getFreshName . FuncId.name) projections
    projectionSorts <- Monad.mapM sort2sort (CstrId.cstrargs cstrId)
    let fields = zipWith (\x y -> MCRL2Defs.Variable { MCRL2Defs.varName = x, MCRL2Defs.varSort = y }) projectionNames projectionSorts
    let newConstructor = MCRL2Defs.Constructor { MCRL2Defs.cstrName = constructorName, MCRL2Defs.fields = fields, MCRL2Defs.recognizer = recognizerName }
    -- Look up the (already created) mCRL2 sort that corresponds with the TXS sort of the constructor:
    (sortName, sort) <- getRegisteredSort (CstrId.cstrsort cstrId)
    registerObject (TxsDefs.IdCstr cstrId) (RegCstr sortName constructorName)
    -- Overwrite the previous declaration of the mCRL2 sort with one with the new constructor:
    let newStructSort = case sort of
                          MCRL2Defs.StructSort constructors -> MCRL2Defs.StructSort (constructors ++ [newConstructor])
                          _ -> MCRL2Defs.StructSort [newConstructor]
    modifySpec $ (\spec -> spec { MCRL2Defs.sorts = Map.insert sortName newStructSort (MCRL2Defs.sorts spec) })
-- constructor2constructor

-- Creates an mCRL2 mapping from a TXS function definition.
-- The body of the function is not being translated here, because it may reference objects that do not yet exist!
function2mapping :: (FuncId.FuncId, FuncDef.FuncDef VarId.VarId) -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Sort)
function2mapping (funcId, FuncDef.FuncDef params _expr) = do
    mappingName <- getFreshName (FuncId.name funcId)
    mappingParams <- Monad.mapM createFreshVar params
    mappingResult <- sort2sort (FuncId.funcsort funcId)
    -- Add a mapping for the function:
    let mappingSort = case mappingParams of
                        [] -> MCRL2Defs.FunctionSort (sortList2multiSort (map MCRL2Defs.varSort mappingParams)) mappingResult
                        _ -> mappingResult
    registerObject (TxsDefs.IdFunc funcId) (RegMapping mappingName)
    return (mappingName, mappingSort)
-- function2mapping

-- Converts a list of mCRL2 sorts into a (binary) tree of multi-sorts:
sortList2multiSort :: [MCRL2Defs.Sort] -> MCRL2Defs.Sort
sortList2multiSort [] = error "Cannot create MultiSort from empty Sort list!"
sortList2multiSort [x] = x
sortList2multiSort (x1:x2:xs) = MCRL2Defs.MultiSort x1 (sortList2multiSort (x2:xs))
-- sortList2multiSort

-- Creates an mCRL2 equation group from a TXS function definition:
function2eqGroup :: (FuncId.FuncId, FuncDef.FuncDef VarId.VarId) -> T2MMonad MCRL2Defs.EquationGroup
function2eqGroup (funcId, FuncDef.FuncDef params expr) = do
    (mappingName, _) <- getRegisteredMapping funcId
    -- Construct the equation:
    mappingParams <- Monad.mapM createFreshVar params
    let mappingRef = MCRL2Defs.DMappingRef mappingName (map (\v -> MCRL2Defs.DVariableRef v) mappingParams)
    funcExpr <- valExpr2dataExpr expr -- Here, all functions must already have a mapping, because they could be referenced!
    let eqn = MCRL2Defs.Equation { MCRL2Defs.lhs = mappingRef, MCRL2Defs.rhs = funcExpr }
    return $ MCRL2Defs.EquationGroup { MCRL2Defs.variables = mappingParams, MCRL2Defs.equations = [eqn] }
-- function2eqGroup

-- Creates a uniquely named action for each channel of a given process:
process2actions :: (ProcId.ProcId, TxsDefs.ProcDef) -> T2MMonad ()
process2actions (procId, TxsDefs.ProcDef chans _params _expr) = do
    actions <- Monad.mapM (createFreshAction (ProcId.name procId)) chans
    modifySpec $ (\spec -> spec { MCRL2Defs.actions = Map.union (MCRL2Defs.actions spec) (Map.fromList actions) })
-- process2actions

-- Creates a uniquely named action for each channel of a given model:
model2actions :: (ModelId.ModelId, TxsDefs.ModelDef) -> T2MMonad ()
model2actions (modelId, TxsDefs.ModelDef inChans outChans syncChans _expr) = do
    inActions <- Monad.mapM (createFreshAction (ModelId.name modelId)) (flatten inChans)
    outActions <- Monad.mapM (createFreshAction (ModelId.name modelId)) (flatten outChans)
    syncActions <- Monad.mapM (createFreshAction (ModelId.name modelId)) (flatten syncChans)
    modifySpec $ (\spec -> spec { MCRL2Defs.actions = Map.union (MCRL2Defs.actions spec) (Map.fromList (inActions ++ outActions ++ syncActions)) })
      where
        flatten :: [Set.Set TxsDefs.ChanId] -> [TxsDefs.ChanId]
        flatten chans = foldl (++) [] (map Set.toList chans)
-- model2actions

-- Creates a uniquely named action from a TXS channel definition:
createFreshAction :: MCRL2Defs.ObjectId -> TxsDefs.ChanId -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Action)
createFreshAction prefix chanId = do
    actionName <- getFreshName prefix
    actionSorts <- Monad.mapM sort2sort (ChanId.chansorts chanId)
    registerObject (TxsDefs.IdChan chanId) (RegAction actionName)
    return $ (actionName, MCRL2Defs.Action actionSorts)
-- createFreshAction

-- Creates an mCRL2 process from a TXS process.
-- The body of the process is not being translated here, because it may reference objects that do not yet exist!
process2processHeader :: (ProcId.ProcId, TxsDefs.ProcDef) -> T2MMonad (MCRL2Defs.ObjectId, MCRL2Defs.Process)
process2processHeader (procId, TxsDefs.ProcDef _chans params _expr) = do
    procName <- getFreshName (ProcId.name procId)
    procParams <- Monad.mapM createFreshVar params
    registerObject (TxsDefs.IdProc procId) (RegProcess procName)
    return $ (procName, MCRL2Defs.Process { MCRL2Defs.processParams = procParams, MCRL2Defs.expr = MCRL2Defs.PDeadlock })
-- process2processHeader

-- Translates the body of a TXS process:
process2processBody :: (ProcId.ProcId, TxsDefs.ProcDef) -> T2MMonad ()
process2processBody (procId, TxsDefs.ProcDef _chans _params expr) = do
    (procName, MCRL2Defs.Process { MCRL2Defs.processParams = procParams }) <- getRegisteredProcess procId
    procExpr <- behaviorExpr2procExpr expr
    let newProcess = MCRL2Defs.Process { MCRL2Defs.processParams = procParams, MCRL2Defs.expr = procExpr }
    modifySpec $ (\spec -> spec { MCRL2Defs.processes = Map.insert procName newProcess (MCRL2Defs.processes spec) })
-- process2processBody

-- Translates a TXS sort to an mCRL2 sort:
sort2sort :: SortId.SortId -> T2MMonad MCRL2Defs.Sort
sort2sort sortId = do
    if sortId == SortId.sortIdBool
    then do return MCRL2Defs.BoolSort
    else if sortId == SortId.sortIdInt
         then do return MCRL2Defs.IntSort
         else do (sortName, _) <- getRegisteredSort sortId
                 return $ MCRL2Defs.SortRef sortName
-- sort2sort

-- Creates a uniquely named mCRL2 variable from a TXS variable:
createFreshVar :: VarId.VarId -> T2MMonad MCRL2Defs.Variable
createFreshVar varId = do
    newVarName <- getFreshName (VarId.name varId)
    newVarSort <- sort2sort (VarId.varsort varId)
    let newVar = MCRL2Defs.Variable { MCRL2Defs.varName = newVarName, MCRL2Defs.varSort = newVarSort }
    registerObject (TxsDefs.IdVar varId) (RegVar newVar)
    return newVar
-- createFreshVar

-- Creates a uniquely named mCRL2 variable from a TXS variable:
getOrCreateFreshVar :: VarId.VarId -> T2MMonad MCRL2Defs.Variable
getOrCreateFreshVar varId = do
    (_varName, var) <- getRegisteredVar varId
    case var of
      MCRL2Defs.MissingVariable -> do createFreshVar varId
      _ -> do return var
-- getOrCreateFreshVar

-- Translates a TXS behavioral expression to an mCRL2 process expression:
behaviorExpr2procExpr :: TxsDefs.BExpr -> T2MMonad MCRL2Defs.PExpr
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Stop) = do
    return $ MCRL2Defs.PDeadlock
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.ActionPref actOffer expr) = do
    let offers = Set.toList (TxsDefs.offers actOffer)
    -- First (always!), create the variables that are introduced (or overwritten?) by the offer!
    -- The variables must exist so that they can be referenced by other components of the expression:
    variables <- Monad.mapM getOrCreateFreshVar (foldl getOfferVariables [] offers)
    constraint <- valExpr2dataExpr (TxsDefs.constraint actOffer) -- TODO optimize by checking if constraint == True
    translatedExpr <- behaviorExpr2procExpr expr
    if offers == []
    then do -- No offers, so many components of the expression can be left out:
            let tauThenExpr = MCRL2Defs.PSeq (MCRL2Defs.PAction MCRL2Defs.ATau) translatedExpr
            return $ MCRL2Defs.PGuard constraint tauThenExpr MCRL2Defs.PDeadlock
    else do -- Otherwise, construct the full expression:
            actionInstances <- Monad.mapM offer2actionInstance offers
            let action = MCRL2Defs.PAction (MCRL2Defs.AExpr actionInstances)
            let actionThenExpr = MCRL2Defs.PSeq action translatedExpr
            let guard = MCRL2Defs.PGuard constraint actionThenExpr MCRL2Defs.PDeadlock
            -- If there are no variables, the sum operator can be left out:
            if variables == []
            then do return guard
            else do return $ MCRL2Defs.PSum variables guard
  where
    -- Determines the variables that are introduced (or overwritten) by a given offer:
    getOfferVariables :: [VarId.VarId] -> TxsDefs.Offer -> [VarId.VarId]
    getOfferVariables soFar offer = soFar ++ (foldl getOfferVariable [] (TxsDefs.chanoffers offer))
    
    -- Helper method to the one above:
    getOfferVariable :: [VarId.VarId] -> TxsDefs.ChanOffer -> [VarId.VarId]
    getOfferVariable soFar (TxsDefs.Quest var) = soFar ++ [var]
    getOfferVariable soFar _ = soFar
    
    -- Constructs an action instance from a given offer.
    -- Multiple action instances can be combined into a multi-action in an action expression:
    offer2actionInstance :: TxsDefs.Offer -> T2MMonad MCRL2Defs.AInstance
    offer2actionInstance offer = do
        (actionName, _action) <- getRegisteredAction (TxsDefs.chanid offer)
        ainstances <- Monad.mapM chanOffer2actionParam (TxsDefs.chanoffers offer)
        return $ MCRL2Defs.AInstance actionName ainstances
    
    -- Helper method to the one above:
    chanOffer2actionParam :: TxsDefs.ChanOffer -> T2MMonad MCRL2Defs.DExpr
    chanOffer2actionParam (TxsDefs.Quest var) = do valExpr2dataExpr (ValExpr.cstrVar var)
    chanOffer2actionParam (TxsDefs.Exclam vexpr) = do valExpr2dataExpr vexpr
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Guard condition ifBranch) = do
    translatedCondition <- valExpr2dataExpr condition
    translatedIfBranch <- behaviorExpr2procExpr ifBranch
    return $ MCRL2Defs.PGuard translatedCondition translatedIfBranch MCRL2Defs.PDeadlock
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Choice choices) = do
    translatedChoices <- Monad.mapM behaviorExpr2procExpr choices
    return $ MCRL2Defs.PChoice translatedChoices
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Parallel chans components) = do
    if chans == []
    then do -- In the absence of any channels, the expression becomes very simple:
            translatedComponents <- Monad.mapM behaviorExpr2procExpr components
            case translatedComponents of
              x:xs -> do -- Return the parallel components (as a tree):
                         return $ foldr MCRL2Defs.PPar x xs
              _ -> do return MCRL2Defs.PDeadlock -- Should not happen!
    else do translatedChans <- Monad.mapM getRegisteredAction chans
            -- For each channel (~=~ action), a fresh temporary action of the same sort is created:
            temporaryActions <- Monad.mapM (\((actionName, _action), chan) -> createFreshAction actionName chan) (zip translatedChans chans)
            -- Relate channels with their temporary counterpart:
            let actionPairs = zip (map fst translatedChans) (map fst temporaryActions)
            -- Translate the parallel components:
            translatedComponents <- Monad.mapM behaviorExpr2procExpr components
            case translatedComponents of
              x:xs -> do -- Construct the full expression:
                         let componentsAsTree = foldr MCRL2Defs.PPar x xs
                         let renaming = MCRL2Defs.PRename (map (\(a, b) -> (b, a)) actionPairs) componentsAsTree
                         let block = MCRL2Defs.PBlock (map fst actionPairs) renaming
                         return $ MCRL2Defs.PComm (map createComm actionPairs) block
              _ -> do return MCRL2Defs.PDeadlock -- Should not happen!
  where
    createComm :: (MCRL2Defs.ObjectId, MCRL2Defs.ObjectId) -> (MCRL2Defs.MultiAction, MCRL2Defs.ObjectId)
    createComm (translatedChan, temporaryAction) = (foldl (\soFar _ -> soFar ++ [translatedChan]) [] components, temporaryAction)
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Enable _expr1 _chanOffers _expr2) = do
    return $ MCRL2Defs.PDeadlock -- TODO
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Disable _expr1 _expr2) = do
    return $ MCRL2Defs.PDeadlock -- TODO
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Interrupt _expr1 _expr2) = do
    return $ MCRL2Defs.PDeadlock -- TODO
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.ProcInst procId [] paramValues) = do
    -- Create the process instantiation:
    (processName, MCRL2Defs.Process { MCRL2Defs.processParams = paramDefs }) <- getRegisteredProcess procId
    translatedParamValues <- Monad.mapM valExpr2dataExpr paramValues
    return $ MCRL2Defs.PInst processName (zip paramDefs translatedParamValues)
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.ProcInst procId chanValues paramValues) = do
    -- Create the process instantiation:
    (processName, MCRL2Defs.Process { MCRL2Defs.processParams = paramDefs }) <- getRegisteredProcess procId
    translatedParamValues <- Monad.mapM valExpr2dataExpr paramValues
    let instantiation = MCRL2Defs.PInst processName (zip paramDefs translatedParamValues)
    -- Create the renaming operator:
    chanDefs <- Monad.mapM getRegisteredAction (ProcId.procchans procId)
    translatedChanValues <- Monad.mapM getRegisteredAction chanValues
    let renaming = MCRL2Defs.PRename (zip (map fst chanDefs) (map fst translatedChanValues)) instantiation
    -- Return the combination:
    return $ renaming
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.Hide chans expr) = do
    translatedChans <- Monad.mapM getRegisteredAction chans
    translatedExpr <- behaviorExpr2procExpr expr
    return $ MCRL2Defs.PHide (map fst translatedChans) translatedExpr
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.ValueEnv _venv _expr) = do
    return $ MCRL2Defs.PDeadlock -- TODO what is this exactly?
behaviorExpr2procExpr (TxsDefs.view -> TxsDefs.StAut _statId _venv _transList) = do
    return $ MCRL2Defs.PDeadlock -- TODO what is this exactly?
behaviorExpr2procExpr _ = do
    return $ MCRL2Defs.PDeadlock -- Should not happen!
-- behaviorExpr2procExpr

-- Translates a TXS value expression to an mCRL2 data expression:
valExpr2dataExpr :: ValExpr.ValExpr VarId.VarId -> T2MMonad MCRL2Defs.DExpr
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconst (ConstDefs.Cbool value)) = do
    return $ MCRL2Defs.DBool value
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconst (ConstDefs.Cint value)) = do
    return $ MCRL2Defs.DInt value
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconst (ConstDefs.Cstring string)) = do
    return $ MCRL2Defs.DList (map (MCRL2Defs.DInt . toInteger . Char.ord) (Text.unpack string))
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconst (ConstDefs.Cregex _value)) = do
    return $ MCRL2Defs.DList [] -- WARNING! Regular expressions are considered to be out of scope!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconst (ConstDefs.Cstr cstrId fieldValues)) = do
    valExpr2dataExpr (ValExpr.cstrCstr cstrId (map ValExpr.cstrConst fieldValues)) -- Delegate!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconst (ConstDefs.Cany sortId)) = do
    newGlobalName <- getFreshName (Text.pack ("g" ++ (Text.unpack (SortId.name sortId))))
    newGlobalSort <- sort2sort sortId
    let newGlobal = MCRL2Defs.Variable { MCRL2Defs.varName = newGlobalName, MCRL2Defs.varSort = newGlobalSort }
    -- Note that the global does not have to be registered, since it will only be referenced once.
    -- It must be declared in mCRL2 though:
    modifySpec $ (\spec -> spec { MCRL2Defs.globals = Map.insert newGlobalName newGlobal (MCRL2Defs.globals spec) })
    return $ MCRL2Defs.DVariableRef newGlobal
valExpr2dataExpr (ValExpr.view -> ValExpr.Vvar var) = do
    (_varName, translatedVar) <- getRegisteredVar var
    return $ MCRL2Defs.DVariableRef translatedVar
valExpr2dataExpr (ValExpr.view -> ValExpr.Vequal lhs rhs) = do
    translatedLhs <- valExpr2dataExpr lhs
    translatedRhs <- valExpr2dataExpr rhs
    return $ MCRL2Defs.DEqual translatedLhs translatedRhs
valExpr2dataExpr (ValExpr.view -> ValExpr.Vite condition ifBranch elseBranch) = do
    translatedCondition <- valExpr2dataExpr condition
    translatedIfBranch <- valExpr2dataExpr ifBranch
    translatedElseBranch <- valExpr2dataExpr elseBranch
    return $ MCRL2Defs.DIfThenElse translatedCondition translatedIfBranch translatedElseBranch
valExpr2dataExpr (ValExpr.view -> ValExpr.Vnot expr) = do
    translatedExpr <- valExpr2dataExpr expr
    return $ MCRL2Defs.DNot translatedExpr
valExpr2dataExpr (ValExpr.view -> ValExpr.Vand conjuncts) = do
    translatedConjuncts <- Monad.mapM valExpr2dataExpr (Set.toList conjuncts)
    case translatedConjuncts of
      x:xs -> do return $ foldr MCRL2Defs.DAnd x xs
      _ -> do return $ MCRL2Defs.DBool True -- Should not happen!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vdivide dividend divisor) = do
    translatedDividend <- valExpr2dataExpr dividend
    translatedDivisor <- valExpr2dataExpr divisor
    return $ MCRL2Defs.DDivide translatedDividend translatedDivisor
valExpr2dataExpr (ValExpr.view -> ValExpr.Vmodulo dividend divisor) = do
    translatedDividend <- valExpr2dataExpr dividend
    translatedDivisor <- valExpr2dataExpr divisor
    return $ MCRL2Defs.DModulo translatedDividend translatedDivisor
valExpr2dataExpr (ValExpr.view -> ValExpr.Vsum freeSum) = do
    translatedFreeSum <- Monad.mapM cOccur2dataExpr (FMX.toDistinctAscOccurListT freeSum)
    case translatedFreeSum of
      x:xs -> do return $ foldr MCRL2Defs.DAdd x xs
      [] -> do return $ MCRL2Defs.DInt 0 -- Should not happen!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vproduct freeProduct) = do
    translatedFreeProduct <- Monad.mapM cOccur2dataExpr (FMX.toDistinctAscOccurListT freeProduct)
    case translatedFreeProduct of
      x:xs -> do return $ foldr MCRL2Defs.DMultiply x xs
      [] -> do return $ MCRL2Defs.DInt 1 -- Should not happen!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vgez expr) = do
    translatedExpr <- valExpr2dataExpr expr
    return $ MCRL2Defs.DGreaterEquals translatedExpr (MCRL2Defs.DInt 0)
valExpr2dataExpr (ValExpr.view -> ValExpr.Vlength string) = do
    translatedString <- valExpr2dataExpr string
    return $ MCRL2Defs.DListSize translatedString
valExpr2dataExpr (ValExpr.view -> ValExpr.Vat string index) = do
    translatedString <- valExpr2dataExpr string
    translatedIndex <- valExpr2dataExpr index
    return $ MCRL2Defs.DListElement translatedString translatedIndex
valExpr2dataExpr (ValExpr.view -> ValExpr.Vconcat strings) = do
    translatedStrings <- Monad.mapM valExpr2dataExpr strings
    case translatedStrings of
      x:xs -> do return $ foldr MCRL2Defs.DListConcatenate x xs
      _ -> do return $ MCRL2Defs.DList [] -- Should not happen!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vstrinre _string _regex) = do
    return $ MCRL2Defs.DList [] -- WARNING! Regular expressions are considered to be out of scope!
valExpr2dataExpr (ValExpr.view -> ValExpr.Vcstr cstrId fieldValues) = do
    (cstrName, MCRL2Defs.Constructor { MCRL2Defs.fields = fields }) <- getRegisteredCstr cstrId
    translatedFieldValues <- Monad.mapM valExpr2dataExpr fieldValues
    return $ MCRL2Defs.DConstructorRef cstrName (zip fields translatedFieldValues)
valExpr2dataExpr (ValExpr.view -> ValExpr.Viscstr cstrId expr) = do
    (_cstrName, MCRL2Defs.Constructor { MCRL2Defs.recognizer = recognizerName }) <- getRegisteredCstr cstrId
    translatedExpr <- valExpr2dataExpr expr
    return $ MCRL2Defs.DRecognizer recognizerName translatedExpr
valExpr2dataExpr (ValExpr.view -> ValExpr.Vaccess cstrId fieldIndex expr) = do
    (_cstrName, MCRL2Defs.Constructor { MCRL2Defs.fields = fields }) <- getRegisteredCstr cstrId
    translatedExpr <- valExpr2dataExpr expr
    return $ MCRL2Defs.DFieldAccess (MCRL2Defs.varName (fields !! fieldIndex)) translatedExpr
valExpr2dataExpr (ValExpr.view -> ValExpr.Vfunc funcId paramValues) = do
    (mappingName, _mappingSort) <- getRegisteredMapping funcId
    translatedParamValues <- Monad.mapM valExpr2dataExpr paramValues
    return $ MCRL2Defs.DMappingRef mappingName translatedParamValues
valExpr2dataExpr (ValExpr.view -> ValExpr.Vpredef _predefKind _funcId _paramValues) = do
    return $ MCRL2Defs.DBool False -- TODO what is this exactly?
valExpr2dataExpr _ = do return $ MCRL2Defs.DBool False
-- valExpr2dataExpr

-- Used exclusively to translate FreeSums and FreeProducts (FreeMonoidXs):
cOccur2dataExpr :: (ValExpr.ValExpr VarId.VarId, Integer) -> T2MMonad MCRL2Defs.DExpr
cOccur2dataExpr (expr, count) = do
    translatedExpr <- valExpr2dataExpr expr
    return $ MCRL2Defs.DMultiply translatedExpr (MCRL2Defs.DInt count)
-- cOccur2dataExpr



