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
showLPEChannelOffer,
showLPEParamEq,
showLPESummand,
showLPEInstance
) where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified FreeMonoidX as FMX
import Constant hiding (sort)
import VarId
import ValExpr
import qualified TxsDefs
import qualified FuncId
import qualified CstrId
import qualified SortId
import qualified ChanId
import LPETypes

showValExpr :: TxsDefs.VExpr -> String
showValExpr      (view -> Vconst (Cbool val))      = show val
showValExpr      (view -> Vconst (Cint val))       = show val
showValExpr      (view -> Vconst (Cstring val))    = show val
showValExpr      (view -> Vconst (Cregex val))     = show val
showValExpr      (view -> Vconst (Ccstr cid pars)) = let newPars = map (showValExpr . cstrConst) pars in
                                                       (Text.unpack (CstrId.name cid)) ++ "(" ++ (separatedList newPars ", ") ++ ")"
showValExpr      (view -> Vconst (Cany sort))      = "ANY " ++ (Text.unpack (SortId.name sort))
showValExpr      (view -> Vvar vid)                = Text.unpack (VarId.name vid)
showValExpr      (view -> Vfunc fid vexps)         = let newVExps = map showValExpr vexps in
                                                      (Text.unpack (FuncId.name fid)) ++ "(" ++ (separatedList newVExps ", ") ++ ")"
showValExpr      (view -> Vcstr cid vexps)         = let newVExps = map showValExpr vexps in
                                                       (Text.unpack (CstrId.name cid)) ++ "(" ++ (separatedList newVExps ", ") ++ ")"
showValExpr      (view -> Viscstr cid vexp)        = let newVExp = showValExpr vexp in
                                                       "(" ++ newVExp ++ " is " ++ (Text.unpack (CstrId.name cid)) ++ ")"
showValExpr      (view -> Vaccess cid p vexp)      = let newVExp = showValExpr vexp in
                                                        (Text.unpack (CstrId.name cid)) ++ "(" ++ newVExp ++ ")[" ++ (show p) ++ "]"
showValExpr      (view -> Vite cond vexp1 vexp2)   = "if " ++ (showValExpr cond) ++ " then " ++ (showValExpr vexp1) ++ " else " ++ (showValExpr vexp2) ++ " end"
showValExpr      (view -> Vdivide t n)             = "(" ++ (showValExpr t) ++ "/" ++ (showValExpr n) ++ ")"
showValExpr      (view -> Vmodulo t n)             = "(" ++ (showValExpr t) ++ "%" ++ (showValExpr n) ++ ")"
showValExpr      (view -> Vgez v)                  = (showValExpr v) ++ ">=0"
showValExpr      (view -> Vsum s)                  = let newVExps = map visitcOccur (FMX.toDistinctAscOccurListT s) in
                                                       "(" ++ (separatedList newVExps "+") ++ ")"
showValExpr      (view -> Vproduct p)              = let newVExps = map visitcOccur (FMX.toDistinctAscOccurListT p) in
                                                       "(" ++ (separatedList newVExps "*") ++ ")"
showValExpr      (view -> Vequal vexp1 vexp2)      = "(" ++ (showValExpr vexp1) ++ "==" ++ (showValExpr vexp2) ++ ")"
showValExpr      (view -> Vand vexps)              = let newVExps = map showValExpr (Set.toList vexps) in
                                                       "(" ++ (separatedList newVExps " && ") ++ ")"
showValExpr      (view -> Vnot vexp)               = "!" ++ (showValExpr vexp)
showValExpr      (view -> Vlength vexp)            = "length(" ++ (showValExpr vexp) ++ ")"
showValExpr      (view -> Vat s p)                 = (showValExpr s) ++ "[" ++ (showValExpr p) ++ "]"
showValExpr      (view -> Vconcat vexps)           = let newVExps = map showValExpr vexps in
                                                       (separatedList newVExps ":")
showValExpr      (view -> Vstrinre s r)            = "regex(" ++ (showValExpr s) ++ ", " ++ (showValExpr r) ++ ")"
-- showValExpr      (view -> Vpredef kd fid vexps)    = let newVExps = map showValExpr vexps
--                                                        cstrPredef kd fid newVExps
showValExpr expr                                   = error ("LPEPrettyPrint.showValExpr not defined for " ++ (show expr))
-- showValExpr

separatedList :: [String] -> String -> String
separatedList [] _ = ""
separatedList [x] _ = x
separatedList (x1:x2:xs) separator = x1 ++ separator ++ (separatedList (x2:xs) separator)

visitcOccur :: (TxsDefs.VExpr, Integer) -> String
visitcOccur (v, 1) = showValExpr v
visitcOccur (v, n) = (showValExpr v) ++ " times " ++ (show n)

showLPEChannelOffer :: LPEChannelOffer -> String
showLPEChannelOffer (chanId, vars) = (Text.unpack (ChanId.name chanId)) ++ (concat (map (\v -> " ? " ++ (Text.unpack (VarId.name v))) vars))

showLPEChannelOffers :: LPEChannelOffers -> String
showLPEChannelOffers [] = ""
showLPEChannelOffers channelOffers = (List.intercalate " | " (map showLPEChannelOffer channelOffers)) ++ " "

showLPEParamEq :: LPEParamEq -> String
showLPEParamEq (varId, expr) = (Text.unpack (VarId.name varId)) ++ " = " ++ (showValExpr expr)

showLPESummand :: LPESummand -> String
showLPESummand (LPESummand channelOffers guard LPEStop) =
    (showLPEChannelOffers channelOffers) ++ "[[ " ++ (showValExpr guard) ++ " ]] >-> STOP"
showLPESummand (LPESummand channelOffers guard (LPEProcInst paramEqs)) =
    (showLPEChannelOffers channelOffers) ++ "[[ " ++ (showValExpr guard) ++ " ]] >-> LPE(" ++ (List.intercalate ", " (map showLPEParamEq paramEqs)) ++ ")"
-- showLPESummand

showChanDecl :: ChanId.ChanId -> String
showChanDecl chanId =
    let chanSortStrings = map (\chansort -> Text.unpack (SortId.name chansort)) (ChanId.chansorts chanId) in
      (Text.unpack (ChanId.name chanId)) ++ " :: " ++ (List.intercalate " # " chanSortStrings)
-- showChanDecl

showLPEInstance :: LPEInstance -> String
showLPEInstance (chanIds, initParamEqs, summands) =
    "LPE[" ++ (List.intercalate "; " (map showChanDecl chanIds)) ++ "] (" ++
    (List.intercalate ", " (map showLPEParamEq initParamEqs)) ++ ") ::=\n        " ++
    (List.intercalate "\n     ## " (map showLPESummand summands)) ++ "\n;"
-- showLPEInstance



