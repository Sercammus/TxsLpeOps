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
showValExpr,
showContextFreeValExpr,
showLPEChannelOffer,
showLPEParamEq,
showLPESummand,
showLPEInstance,
showSubst
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
import LPETypes

showCFValExpr :: Map.Map VarId String -> TxsDefs.VExpr -> String
showCFValExpr _ (view -> Vconst (Cbool val))      = show val
showCFValExpr _ (view -> Vconst (Cint val))       = show val
showCFValExpr _ (view -> Vconst (Cstring val))    = show val
showCFValExpr _ (view -> Vconst (Cregex val))     = show val
showCFValExpr f (view -> Vconst (Ccstr cid pars)) = let newPars = map (showCFValExpr f . cstrConst) pars in
                                                      (Text.unpack (CstrId.name cid)) ++ "(" ++ (separatedList newPars ", ") ++ ")"
showCFValExpr _ (view -> Vconst (Cany sort))      = "ANY " ++ (Text.unpack (SortId.name sort))
showCFValExpr f (view -> Vvar vid)                = f Map.! vid
showCFValExpr f (view -> Vfunc fid vexps)         = let newVExps = map (showCFValExpr f) vexps in
                                                      (Text.unpack (FuncId.name fid)) ++ "(" ++ (separatedList newVExps ", ") ++ ")"
showCFValExpr f (view -> Vcstr cid vexps)         = let newVExps = map (showCFValExpr f) vexps in
                                                      (Text.unpack (CstrId.name cid)) ++ "(" ++ (separatedList newVExps ", ") ++ ")"
showCFValExpr f (view -> Viscstr cid vexp)        = let newVExp = showCFValExpr f vexp in
                                                      "(" ++ newVExp ++ " is " ++ (Text.unpack (CstrId.name cid)) ++ ")"
showCFValExpr f (view -> Vaccess cid p vexp)      = let newVExp = showCFValExpr f vexp in
                                                      (Text.unpack (CstrId.name cid)) ++ "(" ++ newVExp ++ ")[" ++ (show p) ++ "]"
showCFValExpr f (view -> Vite cond vexp1 vexp2)   = "if " ++ (showCFValExpr f cond) ++ " then " ++ (showCFValExpr f vexp1) ++ " else " ++ (showCFValExpr f vexp2) ++ " end"
showCFValExpr f (view -> Vdivide t n)             = "(" ++ (showCFValExpr f t) ++ "/" ++ (showCFValExpr f n) ++ ")"
showCFValExpr f (view -> Vmodulo t n)             = "(" ++ (showCFValExpr f t) ++ "%" ++ (showCFValExpr f n) ++ ")"
showCFValExpr f (view -> Vgez v)                  = (showCFValExpr f v) ++ ">=0"
showCFValExpr f (view -> Vsum s)                  = let newVExps = map (visitcOccur f) (FMX.toDistinctAscOccurListT s) in
                                                      "(" ++ (separatedList newVExps "+") ++ ")"
showCFValExpr f (view -> Vproduct p)              = let newVExps = map (visitcOccur f) (FMX.toDistinctAscOccurListT p) in
                                                      "(" ++ (separatedList newVExps "*") ++ ")"
showCFValExpr f (view -> Vequal vexp1 vexp2)      = "(" ++ (showCFValExpr f vexp1) ++ "==" ++ (showCFValExpr f vexp2) ++ ")"
showCFValExpr f (view -> Vand vexps)              = let newVExps = map (showCFValExpr f) (Set.toList vexps) in
                                                      "(" ++ (separatedList newVExps " && ") ++ ")"
showCFValExpr f (view -> Vnot vexp)               = "not(" ++ (showCFValExpr f vexp) ++ ")"
showCFValExpr f (view -> Vlength vexp)            = "length(" ++ (showCFValExpr f vexp) ++ ")"
showCFValExpr f (view -> Vat s p)                 = (showCFValExpr f s) ++ "[" ++ (showCFValExpr f p) ++ "]"
showCFValExpr f (view -> Vconcat vexps)           = let newVExps = map (showCFValExpr f) vexps in
                                                      (separatedList newVExps ":")
showCFValExpr f (view -> Vstrinre s r)            = "regex(" ++ (showCFValExpr f s) ++ ", " ++ (showCFValExpr f r) ++ ")"
showCFValExpr f (view -> Vpredef kd fid vexps)    = let newVExps = map (showCFValExpr f) vexps in
                                                      (Text.unpack (FuncId.name fid)) ++ "[" ++ (show kd) ++ "](" ++ (separatedList newVExps ", ") ++ ")"
showCFValExpr _ expr                              = error ("LPEPrettyPrint.showCFValExpr not defined for " ++ (show expr))
-- showCFValExpr

visitcOccur :: Map.Map VarId String -> (TxsDefs.VExpr, Integer) -> String
visitcOccur f (v, 1) = showCFValExpr f v
visitcOccur f (v, n) = (showCFValExpr f v) ++ " times " ++ (show n)

showValExpr :: TxsDefs.VExpr -> String
showValExpr expr =
    let f = Map.fromList (map (\v -> (v, Text.unpack (VarId.name v))) (FreeVar.freeVars expr)) in
      showCFValExpr f expr
-- showValExpr

showContextFreeValExpr :: TxsDefs.VExpr -> String
showContextFreeValExpr expr =
    let f = Map.fromList (map (\(v, n) -> (v, "var" ++ (show (n::Integer)))) (zip (FreeVar.freeVars expr) [1..])) in
      showCFValExpr f expr
-- showContextFreeValExpr

separatedList :: [String] -> String -> String
separatedList [] _ = ""
separatedList [x] _ = x
separatedList (x1:x2:xs) separator = x1 ++ separator ++ (separatedList (x2:xs) separator)

showLPEChannelOffer :: LPEChannelOffer -> String
showLPEChannelOffer (chanId, vars) = (Text.unpack (ChanId.name chanId)) ++ (concat (map (\v -> " ? " ++ (Text.unpack (VarId.name v))) vars))

showLPEChannelOffers :: LPEChannelOffers -> String
showLPEChannelOffers [] = ""
showLPEChannelOffers channelOffers = (List.intercalate " | " (map showLPEChannelOffer channelOffers)) ++ " "

showHiddenVars :: [VarId] -> String
showHiddenVars [] = ""
showHiddenVars hiddenVars = "(" ++ (List.intercalate ", " (map (\v -> Text.unpack (VarId.name v)) hiddenVars)) ++ ") "

showLPEParamEq :: (VarId, TxsDefs.VExpr) -> String
showLPEParamEq (varId, expr) = (Text.unpack (VarId.name varId)) ++ " = " ++ (showValExpr expr)

showLPEParamEqs :: LPEParamEqs -> String
showLPEParamEqs paramEqs = List.intercalate ", " (map showLPEParamEq (Map.toList paramEqs))

showProcInst :: LPEProcInst -> String
showProcInst LPEStop = "STOP"
showProcInst (LPEProcInst paramEqs) = "LPE(" ++ (showLPEParamEqs paramEqs) ++ ")"

showLPESummand :: LPESummand -> String
showLPESummand (LPESummand channelVars channelOffers guard procInst) =
    let usedChannelVars = concat (map snd channelOffers) in
    let hiddenChannelVars = Set.toList ((Set.fromList channelVars) Set.\\ (Set.fromList usedChannelVars)) in
      (showLPEChannelOffers channelOffers) ++ (showHiddenVars hiddenChannelVars) ++ "[[ " ++ (showValExpr guard) ++ " ]] >-> " ++ (showProcInst procInst)
-- showLPESummand

showChanDecl :: ChanId.ChanId -> String
showChanDecl chanId =
    let chanSortStrings = map (\chansort -> Text.unpack (SortId.name chansort)) (ChanId.chansorts chanId) in
      (Text.unpack (ChanId.name chanId)) ++ " :: " ++ (List.intercalate " # " chanSortStrings)
-- showChanDecl

showLPEInstance :: LPEInstance -> String
showLPEInstance (chanIds, initParamEqs, summands) =
    "LPE[" ++ (List.intercalate "; " (map showChanDecl chanIds)) ++ "] (" ++
    (showLPEParamEqs initParamEqs) ++ ") ::=\n        " ++
    (List.intercalate "\n     ## " (map showLPESummand (Set.toList summands))) ++ "\n;"
-- showLPEInstance

showSubst :: Map.Map VarId TxsDefs.VExpr -> String
showSubst subst = "[" ++ (List.intercalate ", " (map (\(p, v) -> (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr v)) (Map.toList subst))) ++ "]"

