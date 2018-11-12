{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEPrettyPrint
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
module LPEPrettyPrint (
showLPEInstance,
showContextFreeLPEInstance,
showLPESummand,
showContextFreeLPESummand,
showSubst,
showValExpr,
showContextFreeValExpr,
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified FreeMonoidX as FMX
import Constant hiding (sort)
import VarId
import ValExpr hiding (subst)
import qualified TxsDefs
import qualified FuncId
import qualified CstrId
import qualified SortId
import qualified ChanId
import qualified FreeVar
import LPETypeDefs

type VarContext = Map.Map VarId String

createDefaultContextFromVarList :: [VarId] -> VarContext
createDefaultContextFromVarList = createDefaultContextFromVars . Set.fromList

createDefaultContextFromVars :: Set.Set VarId -> VarContext
createDefaultContextFromVars = Map.fromSet (Text.unpack . VarId.name)

createFreeContextFromVarList :: String -> [VarId] -> VarContext
createFreeContextFromVarList prefix vars = Map.fromList (map (\(v, n) -> (v, prefix ++ show (n::Integer))) (zip vars [1..]))

createFreeContextFromVars :: String -> Set.Set VarId -> VarContext
createFreeContextFromVars prefix = createFreeContextFromVarList prefix . Set.toList

getLPEInstanceFreeContext :: LPEInstance -> VarContext
getLPEInstanceFreeContext lpe@(_, initParamEqs, _) =
    let lpeParams = Map.keysSet initParamEqs in
    let lpeVars = getLPEInstanceVariables lpe Set.\\ lpeParams in
      Map.union (createFreeContextFromVars "par" lpeParams) (createFreeContextFromVars "var" lpeVars)
-- getLPEInstanceContext

getLPESummandFreeContext :: LPESummand -> VarContext
getLPESummandFreeContext summand = createFreeContextFromVars "var" (getLPESummandVariables summand)

-- Lists all variables that occur in an LPE:
getLPEInstanceVariables :: LPEInstance -> Set.Set VarId
getLPEInstanceVariables (_, initParamEqs, summands) =
    Set.union (getParamEqsVariables initParamEqs) (Set.unions (map getLPESummandVariables (Set.toList summands)))
-- getLPEInstanceVariables

getLPESummandVariables :: LPESummand -> Set.Set VarId
getLPESummandVariables (LPESummand channelVars channelOffers guard procInst) =
    Set.unions ([Set.fromList channelVars, Set.fromList (FreeVar.freeVars guard), getProcInstVariables procInst] ++ map (Set.fromList . snd) channelOffers)
-- getLPESummandVariables

getProcInstVariables :: LPEProcInst -> Set.Set VarId
getProcInstVariables LPEStop = Set.empty
getProcInstVariables (LPEProcInst eqs) = getParamEqsVariables eqs

getParamEqsVariables :: LPEParamEqs -> Set.Set VarId
getParamEqsVariables eqs = Set.union (Map.keysSet eqs) (Set.unions (map (Set.fromList . FreeVar.freeVars) (Map.elems eqs)))

-- Shows an LPE in the default 'context'; that is,
-- variables are displayed using their actual names:
showLPEInstance :: LPEInstance -> String
showLPEInstance lpe = showCFLPEInstance (createDefaultContextFromVars (getLPEInstanceVariables lpe)) lpe

-- Shows an LPE in a 'free context'; that is,
-- fresh (short) names are introduces for each unique variable, and those names are used to display them:
showContextFreeLPEInstance :: LPEInstance -> String
showContextFreeLPEInstance lpe = showCFLPEInstance (getLPEInstanceFreeContext lpe) lpe

-- Shows an LPE in the specified 'context'; that is,
-- using specific names for specific variables when they occur:
showCFLPEInstance :: VarContext -> LPEInstance -> String
showCFLPEInstance f (chanIds, initParamEqs, summands) =
    "LPE[" ++ List.intercalate "; " (map showChanDecl chanIds) ++ "] (" ++
    showParamEqs initParamEqs ++ ") ::=\n        " ++
    List.intercalate "\n     ## " (map (showCFLPESummand f) (Set.toList summands)) ++ "\n;"
  where
    showChanDecl :: ChanId.ChanId -> String
    showChanDecl chanId =
        let chanSortStrings = map (Text.unpack . SortId.name) (ChanId.chansorts chanId) in
          Text.unpack (ChanId.name chanId) ++ " :: " ++ List.intercalate " # " chanSortStrings
    -- showChanDecl
    
    showParamEqs :: LPEParamEqs -> String
    showParamEqs paramEqs = List.intercalate ", " (map showParamEq (Map.toList paramEqs))
    
    showParamEq :: (VarId, TxsDefs.VExpr) -> String
    showParamEq (varId, expr) = Text.unpack (VarId.name varId) ++ " = " ++ showCFValExpr f expr
-- showCFLPEInstance

-- Shows a summand in the default 'context'; that is,
-- variables are displayed using their actual names:
showLPESummand :: LPESummand -> String
showLPESummand summand = showCFLPESummand (createDefaultContextFromVars (getLPESummandVariables summand)) summand

-- Shows a summand in a 'free context'; that is,
-- fresh (short) names are introduces for each unique variable, and those names are used to display them:
showContextFreeLPESummand :: LPESummand -> String
showContextFreeLPESummand summand = showCFLPESummand (getLPESummandFreeContext summand) summand

-- Shows a summand in the specified 'context'; that is,
-- using specific names for specific variables when they occur:
showCFLPESummand :: VarContext -> LPESummand -> String
showCFLPESummand f (LPESummand channelVars channelOffers guard procInst) =
    let usedChannelVars = concatMap snd channelOffers in
    let hiddenChannelVars = Set.toList (Set.fromList channelVars Set.\\ Set.fromList usedChannelVars) in
      showChannelOffers channelOffers ++
      showHiddenVars hiddenChannelVars ++
      "[[ " ++ showCFValExpr f guard ++ " ]] >-> " ++ showProcInst procInst
  where
    showChannelOffers :: LPEChannelOffers -> String
    showChannelOffers [] = ""
    showChannelOffers offers = List.intercalate " | " (map showChannelOffer offers) ++ " "
    
    showChannelOffer :: LPEChannelOffer -> String
    showChannelOffer (chanId, vars) = Text.unpack (ChanId.name chanId) ++ concatMap (\v -> " ? " ++ f Map.! v) vars
    
    showHiddenVars :: [VarId] -> String
    showHiddenVars [] = ""
    showHiddenVars hiddenVars = "(" ++ List.intercalate ", " (map (f Map.!) hiddenVars) ++ ") "
    
    showProcInst :: LPEProcInst -> String
    showProcInst LPEStop = "STOP"
    showProcInst (LPEProcInst paramEqs) = "LPE(" ++ showParamEqs paramEqs ++ ")"
    
    showParamEqs :: LPEParamEqs -> String
    showParamEqs paramEqs = List.intercalate ", " (map showParamEq (Map.toList paramEqs))
    
    showParamEq :: (VarId, TxsDefs.VExpr) -> String
    showParamEq (varId, expr) = f Map.! varId ++ " = " ++ showCFValExpr f expr
-- showCFLPESummand

-- Shows the given expression in the default 'context'; that is,
-- variables are displayed using their actual names:
showValExpr :: TxsDefs.VExpr -> String
showValExpr expr = showCFValExpr (createDefaultContextFromVarList (FreeVar.freeVars expr)) expr

-- Shows the given expression in a 'free context'; that is,
-- fresh (short) names are introduces for each unique variable, and those names are used to display them:
showContextFreeValExpr :: TxsDefs.VExpr -> String
showContextFreeValExpr expr =
    showCFValExpr (createFreeContextFromVarList "var" (FreeVar.freeVars expr)) expr
-- showContextFreeValExpr

-- Shows a substitution:
showSubst :: Map.Map VarId TxsDefs.VExpr -> String
showSubst subst = "[" ++ List.intercalate ", " (map (\(p, v) -> Text.unpack (VarId.name p) ++ " := " ++ showValExpr v) (Map.toList subst)) ++ "]"

-- Shows the given expression in the specified 'context'; that is,
-- using specific names for specific variables when they occur:
showCFValExpr :: VarContext -> TxsDefs.VExpr -> String
showCFValExpr _ (view -> Vconst (Cbool val))      = show val
showCFValExpr _ (view -> Vconst (Cint val))       = show val
showCFValExpr _ (view -> Vconst (Cstring val))    = show val
showCFValExpr _ (view -> Vconst (Cregex val))     = show val
showCFValExpr f (view -> Vconst (Ccstr cid pars)) = let newPars = map (showCFValExpr f . cstrConst) pars in
                                                      Text.unpack (CstrId.name cid) ++ "(" ++ List.intercalate ", " newPars ++ ")"
showCFValExpr _ (view -> Vconst (Cany sort))      = "ANY " ++ Text.unpack (SortId.name sort)
showCFValExpr f (view -> Vvar vid)                = f Map.! vid
showCFValExpr f (view -> Vfunc fid vexps)         = let newVExps = map (showCFValExpr f) vexps in
                                                      Text.unpack (FuncId.name fid) ++ "(" ++ List.intercalate ", " newVExps ++ ")"
showCFValExpr f (view -> Vcstr cid vexps)         = let newVExps = map (showCFValExpr f) vexps in
                                                      Text.unpack (CstrId.name cid) ++ "(" ++ List.intercalate ", " newVExps ++ ")"
showCFValExpr f (view -> Viscstr cid vexp)        = let newVExp = showCFValExpr f vexp in
                                                      "(" ++ newVExp ++ " is " ++ Text.unpack (CstrId.name cid) ++ ")"
showCFValExpr f (view -> Vaccess cid p vexp)      = let newVExp = showCFValExpr f vexp in
                                                      Text.unpack (CstrId.name cid) ++ "(" ++ newVExp ++ ")[" ++ show p ++ "]"
showCFValExpr f (view -> Vite cond vexp1 vexp2)   = "if " ++ showCFValExpr f cond ++ " then " ++ showCFValExpr f vexp1 ++ " else " ++ showCFValExpr f vexp2 ++ " end"
showCFValExpr f (view -> Vdivide t n)             = "(" ++ showCFValExpr f t ++ "/" ++ showCFValExpr f n ++ ")"
showCFValExpr f (view -> Vmodulo t n)             = "(" ++ showCFValExpr f t ++ "%" ++ showCFValExpr f n ++ ")"
showCFValExpr f (view -> Vgez v)                  = showCFValExpr f v ++ ">=0"
showCFValExpr f (view -> Vsum s)                  = let newVExps = map (visitcOccur f) (FMX.toDistinctAscOccurListT s) in
                                                      "(" ++ List.intercalate "+" newVExps ++ ")"
showCFValExpr f (view -> Vproduct p)              = let newVExps = map (visitcOccur f) (FMX.toDistinctAscOccurListT p) in
                                                      "(" ++ List.intercalate "*" newVExps ++ ")"
showCFValExpr f (view -> Vequal vexp1 vexp2)      = "(" ++ showCFValExpr f vexp1 ++ "==" ++ showCFValExpr f vexp2 ++ ")"
showCFValExpr f (view -> Vand vexps)              = let newVExps = map (showCFValExpr f) (Set.toList vexps) in
                                                      "(" ++ List.intercalate " && " newVExps ++ ")"
showCFValExpr f (view -> Vnot vexp)               = "not(" ++ showCFValExpr f vexp ++ ")"
showCFValExpr f (view -> Vlength vexp)            = "length(" ++ showCFValExpr f vexp ++ ")"
showCFValExpr f (view -> Vat s p)                 = showCFValExpr f s ++ "[" ++ showCFValExpr f p ++ "]"
showCFValExpr f (view -> Vconcat vexps)           = let newVExps = map (showCFValExpr f) vexps in
                                                      List.intercalate ":" newVExps
showCFValExpr f (view -> Vstrinre s r)            = "regex(" ++ showCFValExpr f s ++ ", " ++ showCFValExpr f r ++ ")"
showCFValExpr f (view -> Vpredef kd fid vexps)    = let newVExps = map (showCFValExpr f) vexps in
                                                      Text.unpack (FuncId.name fid) ++ "[" ++ show kd ++ "](" ++ List.intercalate ", " newVExps ++ ")"
showCFValExpr _ expr                              = error ("LPEPrettyPrint.showCFValExpr not defined for " ++ show expr)
-- showCFValExpr

-- Helper function to showCFValExpr:
visitcOccur :: VarContext -> (TxsDefs.VExpr, Integer) -> String
visitcOccur f (v, 1) = showCFValExpr f v
visitcOccur f (v, n) = showCFValExpr f v ++ " times " ++ show n

