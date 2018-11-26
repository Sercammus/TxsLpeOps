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
showLPEModel,
showLPEProcess,
showLPESummand,
showLPEParamEqs,
showValExpr,
showAbbrevLPEModel,
showAbbrevLPEProcess,
showAbbrevLPESummand,
showAbbrevValExpr,
showSubst
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified FuncId
import qualified CstrId
import qualified SortId
import qualified SortOf
import qualified ChanId
import qualified VarId
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           TxsShow
import           LPETypeDefs
import           ValExprVisitor
import           LPEContexts

showLPEModel :: LPEModel -> String
showLPEModel model = showLPEModelInContext (getModelContext model) model

showAbbrevLPEModel :: LPEModel -> String
showAbbrevLPEModel model = showLPEModelInContext (getAbbrevModelContext model) model

showLPEModelInContext :: LPEContext -> LPEModel -> String
showLPEModelInContext f (_, process@(chanIds, initParamEqs, _)) =
    let orderedParams = Map.keys initParamEqs in
      showLPEProcessExactly f process orderedParams True ++
      "MODELDEF Model ::=\n" ++
      "    CHAN IN" ++ "\n" ++
      "    CHAN OUT" ++ "\n" ++
      "    BEHAVIOR LPE[" ++ List.intercalate ", " (map (Text.unpack . ChanId.name) chanIds) ++ "]" ++
      "(" ++ List.intercalate ", " (map (showValExprInContext f) (paramEqsLookup orderedParams initParamEqs)) ++ ")" ++
      "\nENDDEF\n"
-- showLPEModelInContext

showLPEProcess :: LPEProcess -> String
showLPEProcess lpe = showLPEProcessInContext (getProcessContext lpe) lpe

showAbbrevLPEProcess :: LPEProcess -> String
showAbbrevLPEProcess lpe = showLPEProcessInContext (getAbbrevProcessContext lpe) lpe

showLPEProcessInContext :: LPEContext -> LPEProcess -> String
showLPEProcessInContext f lpe@(_, initParamEqs, _) = showLPEProcessExactly f lpe (Map.keys initParamEqs) False

showLPEProcessExactly :: LPEContext -> LPEProcess -> [VarId.VarId] -> Bool -> String
showLPEProcessExactly f (chanIds, initParamEqs, summands) orderedParams initParamValueFlag =
    "PROCDEF LPE[" ++ List.intercalate "; " (map showChanDecl chanIds) ++ "]" ++
    "(" ++ List.intercalate ", " (map showParamDecl orderedParams) ++ ") ::=\n        " ++
    List.intercalate "\n     ## " (map (showLPESummandInContext f) (Set.toList summands)) ++
    "\nENDDEF\n"
  where
    showChanDecl :: ChanId.ChanId -> String
    showChanDecl chanId =
        let chanSortStrings = map pshow (ChanId.chansorts chanId) in
          Text.unpack (ChanId.name chanId) ++ " :: " ++ List.intercalate " # " chanSortStrings
    -- showChanDecl
    
    showParamDecl :: VarId.VarId -> String
    showParamDecl varId = f Map.! (TxsDefs.IdVar varId) ++ " :: " ++ pshow (SortOf.sortOf varId) ++ if initParamValueFlag then showValExprInContext f (initParamEqs Map.! varId) else ""
-- showLPEProcessExactly

showLPESummand :: LPESummand -> String
showLPESummand summand = showLPESummandInContext (getSummandContext summand) summand

showAbbrevLPESummand :: LPESummand -> String
showAbbrevLPESummand summand = showLPESummandInContext (getAbbrevSummandContext summand) summand

showLPESummandInContext :: LPEContext -> LPESummand -> String
showLPESummandInContext f (LPESummand channelVars channelOffers guard paramEqs) =
    let usedChannelVars = concatMap snd channelOffers in
    let hiddenChannelVars = Set.toList (Set.fromList channelVars Set.\\ Set.fromList usedChannelVars) in
      showChannelOffers channelOffers ++
      showHiddenVars hiddenChannelVars ++
      "[[ " ++ showValExprInContext f guard ++ " ]] >-> LPE(" ++ showLPEParamEqs f paramEqs ++ ")"
  where
    showChannelOffers :: LPEChannelOffers -> String
    showChannelOffers [] = ""
    showChannelOffers offers = List.intercalate " | " (map showChannelOffer offers) ++ " "
    
    showChannelOffer :: LPEChannelOffer -> String
    showChannelOffer (chanId, vars) = Text.unpack (ChanId.name chanId) ++ concatMap (\v -> " ? " ++ f Map.! (TxsDefs.IdVar v)) vars
    
    showHiddenVars :: [VarId.VarId] -> String
    showHiddenVars [] = ""
    showHiddenVars hiddenVars = "(" ++ List.intercalate ", " (map (\v -> f Map.! (TxsDefs.IdVar v)) hiddenVars) ++ ") "
-- showLPESummandInContext

showLPEParamEqs :: LPEContext -> LPEParamEqs -> String
showLPEParamEqs f eqs = List.intercalate ", " (map showParamEq (Map.toList eqs))
  where
    showParamEq :: (VarId.VarId, TxsDefs.VExpr) -> String
    showParamEq (varId, expr) = f Map.! (TxsDefs.IdVar varId) ++ " = " ++ showValExprInContext f expr
-- showParamEq

showValExpr :: TxsDefs.VExpr -> String
showValExpr expr = showValExprInContext (getValExprContext expr) expr

showAbbrevValExpr :: TxsDefs.VExpr -> String
showAbbrevValExpr expr = showValExprInContext (getAbbrevValExprContext expr) expr

showSubst :: Map.Map VarId.VarId TxsDefs.VExpr -> String
showSubst subst = "[" ++ List.intercalate ", " (map (\(p, v) -> Text.unpack (VarId.name p) ++ " := " ++ showValExpr v) (Map.toList subst)) ++ "]"

showValExprInContext :: LPEContext -> TxsDefs.VExpr -> String
showValExprInContext f = customData . visitValExpr showVisitor
  where
    showVisitor :: [ValExprVisitorOutput String] -> TxsDefs.VExpr -> ValExprVisitorOutput String
    showVisitor subExps expr =
        let pars = map customData subExps in
        let str = case expr of
                    (view -> Vconst (Cbool val))      -> show val
                    (view -> Vconst (Cint val))       -> show val
                    (view -> Vconst (Cstring val))    -> show val
                    (view -> Vconst (Cregex val))     -> show val
                    (view -> Vconst (Ccstr cid _))    -> Text.unpack (CstrId.name cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vconst (Cany sort))      -> "ANY " ++ Text.unpack (SortId.name sort)
                    (view -> Vvar vid)                -> f Map.! (TxsDefs.IdVar vid)
                    (view -> Vfunc fid _)             -> Text.unpack (FuncId.name fid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vcstr cid _)             -> Text.unpack (CstrId.name cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Viscstr cid _)           -> "is" ++ Text.unpack (CstrId.name cid) ++ "(" ++ head pars ++ ")"
                    (view -> Vaccess cid p _)         -> Text.unpack (FuncId.name (CstrId.cstrargs cid !! p)) ++ "(" ++ head pars ++ ")"
                    (view -> Vite _ _ _)              -> "IF " ++ head pars ++ " THEN " ++ pars !! 1 ++ " ELSE " ++ pars !! 2 ++ " ENDIF"
                    (view -> Vdivide _ _)             -> "(" ++ head pars ++ "/" ++ pars !! 1 ++ ")"
                    (view -> Vmodulo _ _)             -> "(" ++ head pars ++ "%" ++ pars !! 1 ++ ")"
                    (view -> Vgez _)                  -> head pars ++ ">=0"
                    (view -> Vsum _)                  -> "(" ++ List.intercalate "+" (map (showMultElem "*") subExps) ++ ")"
                    (view -> Vproduct _)              -> "(" ++ List.intercalate "*" (map (showMultElem "^") subExps) ++ ")"
                    (view -> Vequal _ _)              -> "(" ++ head pars ++ "==" ++ pars !! 1 ++ ")"
                    (view -> Vand _)                  -> "(" ++ List.intercalate " && " pars ++ ")"
                    (view -> Vnot _)                  -> "not(" ++ head pars ++ ")"
                    (view -> Vlength _)               -> "length(" ++ head pars ++ ")"
                    (view -> Vat _ _)                 -> head pars ++ "[" ++ pars !! 1 ++ "]"
                    (view -> Vconcat _)               -> List.intercalate ":" pars
                    (view -> Vstrinre _ _)            -> "regex(" ++ head pars ++ ", " ++ pars !! 1 ++ ")"
                    (view -> Vpredef _ fid _)         -> Text.unpack (FuncId.name fid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    _                                 -> error ("ShowValExprInContext.showVisitor not defined for " ++ show expr ++ "!")
        in ValExprVisitorOutput expr 1 str
    -- showVisitor
    
    showMultElem :: String -> ValExprVisitorOutput String -> String
    showMultElem op subExp =
        let mult = multiplicity subExp in
          customData subExp ++ if mult /= 1 then op ++ show mult else ""
-- showValExprInContext


