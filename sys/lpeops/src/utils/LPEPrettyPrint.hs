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
showSubst,
showLPEModel,
showLPEProcess,
showLPESummand,
showLPEParamEqs,
showValExpr,
showAbbrevLPEModel,
showAbbrevLPEProcess,
showAbbrevLPESummand,
showAbbrevValExpr
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified SortId
import qualified CstrId
import qualified CstrDef
import qualified FuncId
import qualified FuncDef
import qualified VarId
import qualified ChanId
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           LPETypeDefs
import           LPEContexts
import           ValExprVisitor
--import           ValFactory
--import           Debug.Trace

mapGet :: (Show a, Ord a) => Map.Map a b -> a -> b
mapGet m k =
    --trace ("mapGet(" ++ (show k) ++ ")") (
      Maybe.fromMaybe (error ("Could not find " ++ show k ++ " in map!")) (m Map.!? k)
    --)
-- mapGet

showSubst :: Map.Map VarId.VarId TxsDefs.VExpr -> String
showSubst subst = "[" ++ List.intercalate ", " (map (\(p, v) -> Text.unpack (VarId.name p) ++ " := " ++ showValExpr v) (Map.toList subst)) ++ "]"

showLPEModel :: LPEModel -> String
showLPEModel model = showLPEModelInContext (getModelContext model) model

showAbbrevLPEModel :: LPEModel -> String
showAbbrevLPEModel model = showLPEModelInContext (getAbbrevModelContext model) model

showLPEModelInContext :: LPEContext -> LPEModel -> String
showLPEModelInContext f (tdefs, process@(chanIds, initParamEqs, _)) =
    let orderedParams = Map.keys initParamEqs in
      showTypeDefs f (Map.toList (TxsDefs.cstrDefs tdefs)) ++
      showFuncDefs f (TxsDefs.funcDefs tdefs) ++
      showChanDefs f chanIds ++
      showLPEProcessExactly f process orderedParams False ++
      "MODELDEF Model ::=\n" ++ showChanRef "CHAN IN" chanIds ++ showChanRef "CHAN OUT" [] ++ -- TODO how do we distinguish input channels from output channels?
      "    BEHAVIOUR LPE[" ++ List.intercalate ", " (map (showChanId f) chanIds) ++ "]" ++
      "(" ++ List.intercalate ", " (map (showValExprInContext f) (paramEqsLookup orderedParams initParamEqs)) ++ ")" ++
      "\nENDDEF\n"
  where
    showChanRef :: String -> [ChanId.ChanId] -> String
    showChanRef caption [] = "    " ++ caption ++ "\n"
    showChanRef caption cids = "    " ++ caption ++ " " ++ List.intercalate ", " (map (showChanId f) cids) ++ "\n"
-- showLPEModelInContext

showChanDefs :: LPEContext -> [ChanId.ChanId] -> String
showChanDefs _ [] = ""
showChanDefs f cids =
    "CHANDEF ChanDefs\n" ++ -- From tests, it does not seem to matter what name is used here.
    "    ::= " ++ List.intercalate "\n      ; " (map (showChanDecl f) cids) ++ "\n" ++
    "ENDDEF\n"
-- showChanDefs

showChanDecl :: LPEContext -> ChanId.ChanId -> String
showChanDecl f chanId =
    if null (ChanId.chansorts chanId)
    then showChanId f chanId
    else showChanId f chanId ++ " :: " ++ List.intercalate " # " (map (showSortId f) (ChanId.chansorts chanId))
-- showChanDecl

showTypeDefs :: LPEContext -> [(CstrId.CstrId, CstrDef.CstrDef)] -> String
showTypeDefs f cstrdefs =
    let cstrSortIds = Set.fromList (concatMap extractCstrSortIds (Map.keys f)) in
      concatMap showCstrSortId (Set.toList cstrSortIds)
  where
    extractCstrSortIds :: TxsDefs.Ident -> [SortId.SortId]
    extractCstrSortIds (TxsDefs.IdCstr cid) = [CstrId.cstrsort cid]
    extractCstrSortIds _ = []
    
    showCstrSortId :: SortId.SortId -> String
    showCstrSortId cstrSortId =
        let cstrs = [ (c, d) | (c, d) <- cstrdefs, CstrId.cstrsort c == cstrSortId ] in
          case cstrs of
            [] -> "TYPEDEF " ++ mapGet f (TxsDefs.IdSort cstrSortId) ++ " ENDDEF" -- Implicit type, not allowed in TorXakis but whatever
            _ -> "TYPEDEF " ++ mapGet f (TxsDefs.IdSort cstrSortId) ++ " ::= " ++ List.intercalate " | " (map showCstrDef cstrs) ++ " ENDDEF\n"
    -- showCstrSortId
    
    showCstrDef :: (CstrId.CstrId, CstrDef.CstrDef) -> String
    showCstrDef (cid, CstrDef.CstrDef _ accs) =
        case accs of
          [] -> mapGet f (TxsDefs.IdCstr cid)
          _ -> mapGet f (TxsDefs.IdCstr cid) ++ " { " ++ List.intercalate "; " (map (showAccessor cid) accs) ++ " }"
    --showCstrDef
    
    showAccessor :: CstrId.CstrId -> FuncId.FuncId -> String
    showAccessor cid acc = showAccessorId f cid (FuncId.name acc) ++ " :: " ++ showSortId f (FuncId.funcsort acc)
-- showTypeDefs

showFuncDefs :: LPEContext -> Map.Map FuncId.FuncId (FuncDef.FuncDef VarId.VarId) -> String
showFuncDefs f funcdefs =
    let funcIds = Set.fromList (concatMap extractFuncIds (Map.keys f)) in
      concatMap showFuncDef (Set.toList funcIds)
  where
    extractFuncIds :: TxsDefs.Ident -> [FuncId.FuncId]
    extractFuncIds (TxsDefs.IdFunc fid) = [fid]
    extractFuncIds _ = []
    
    showFuncDef :: FuncId.FuncId -> String
    showFuncDef fid =
        case funcdefs Map.!? fid of
          Just (FuncDef.FuncDef params body) ->
            "FUNCDEF " ++ showFuncId f fid ++ "(" ++ List.intercalate "; " (map showParamDecl params) ++ ") :: " ++ showSortId f (FuncId.funcsort fid) ++ " ::= " ++ showValExprInContext f body ++ " ENDDEF\n"
          Nothing -> ""
    -- showFuncDef
    
    showParamDecl :: VarId.VarId -> String
    showParamDecl varId = showVarId f varId ++ " :: " ++ showSortId f (VarId.varsort varId)
-- showFuncDefs

showLPEProcess :: LPEProcess -> String
showLPEProcess lpe = showLPEProcessInContext (getProcessContext lpe) lpe

showAbbrevLPEProcess :: LPEProcess -> String
showAbbrevLPEProcess lpe = showLPEProcessInContext (getAbbrevProcessContext lpe) lpe

showLPEProcessInContext :: LPEContext -> LPEProcess -> String
showLPEProcessInContext f lpe@(_, initParamEqs, _) = showLPEProcessExactly f lpe (Map.keys initParamEqs) True

showLPEProcessExactly :: LPEContext -> LPEProcess -> [VarId.VarId] -> Bool -> String
showLPEProcessExactly f (chanIds, initParamEqs, summands) orderedParams initParamValueFlag =
    "PROCDEF LPE[" ++ List.intercalate "; " (map (showChanDecl f) chanIds) ++ "]" ++
    "(" ++ List.intercalate "; " (map showParamDecl orderedParams) ++ ") ::=\n        " ++
    List.intercalate "\n     ## " (map (showLPESummandInContext f chanIds) (Set.toList summands)) ++
    "\nENDDEF\n"
  where
    showParamDecl :: VarId.VarId -> String
    showParamDecl varId =
        showVarId f varId ++ " :: " ++ showSortId f (VarId.varsort varId) ++
        if initParamValueFlag then " = " ++ showValExprInContext f (initParamEqs Map.! varId) else ""
    -- showParamDecl
-- showLPEProcessExactly

showLPESummand :: LPESummand -> String
showLPESummand summand = showLPESummandInContext (getSummandContext summand) [] summand

showAbbrevLPESummand :: LPESummand -> String
showAbbrevLPESummand summand = showLPESummandInContext (getAbbrevSummandContext summand) [] summand

showLPESummandInContext :: LPEContext -> [ChanId.ChanId] -> LPESummand -> String
showLPESummandInContext f chanIds (LPESummand channelVars channelOffers guard paramEqs) =
    let usedChannelVars = concatMap snd channelOffers in
    let hiddenChannelVars = Set.toList (Set.fromList channelVars Set.\\ Set.fromList usedChannelVars) in
      showChannelOffers channelOffers ++
      showHiddenVars hiddenChannelVars ++
      "[[ " ++ showValExprInContext f guard ++ " ]] >-> LPE" ++ showChanRefs chanIds ++ "(" ++ showLPEParamEqs f paramEqs ++ ")"
  where
    showChannelOffers :: LPEChannelOffers -> String
    showChannelOffers [] = ""
    showChannelOffers offers = List.intercalate " | " (map showChannelOffer offers) ++ " "
    
    showChannelOffer :: LPEChannelOffer -> String
    showChannelOffer (chanId, vars) = showChanId f chanId ++ concatMap (\v -> " ? " ++ showVarId f v ++ " :: " ++ showSortId f (VarId.varsort v)) vars
    
    showChanRefs :: [ChanId.ChanId] -> String
    showChanRefs [] = ""
    showChanRefs cids = "[" ++ List.intercalate ", " (map (showChanId f) cids) ++ "]"
    
    showHiddenVars :: [VarId.VarId] -> String
    showHiddenVars [] = ""
    showHiddenVars hiddenVars = "(" ++ List.intercalate ", " (map (showVarId f) hiddenVars) ++ ") "
-- showLPESummandInContext

showLPEParamEqs :: LPEContext -> LPEParamEqs -> String
showLPEParamEqs f eqs = List.intercalate ", " (map showParamEq (Map.toList eqs))
  where
    showParamEq :: (VarId.VarId, TxsDefs.VExpr) -> String
    --showParamEq (varId, expr) = mapGet f TxsDefs.IdVar varId ++ " = " ++ showValExprInContext f expr
    showParamEq (_varId, expr) = showValExprInContext f expr
-- showParamEq

showValExpr :: TxsDefs.VExpr -> String
showValExpr expr = showValExprInContext (getValExprContext expr) expr

showAbbrevValExpr :: TxsDefs.VExpr -> String
showAbbrevValExpr expr = showValExprInContext (getAbbrevValExprContext expr) expr

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
                    (view -> Vconst (Cregex val))     -> "REGEX('" ++ Text.unpack val ++ "')"
                    (view -> Vconst (Ccstr cid _))    -> mapGet f (TxsDefs.IdCstr cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vconst (Cany sort))      -> "ANY " ++ showSortId f sort
                    (view -> Vvar vid)                -> showVarId f vid
                    (view -> Vfunc fid _)             -> showFuncId f fid ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vcstr cid _)             -> mapGet f (TxsDefs.IdCstr cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Viscstr cid _)           -> "is" ++ mapGet f (TxsDefs.IdCstr cid) ++ "(" ++ head pars ++ ")"
                    (view -> Vaccess cid n _ _)       -> showAccessorId f cid n ++ "(" ++ head pars ++ ")"
                    (view -> Vite{})                  -> "IF " ++ head pars ++ " THEN " ++ pars !! 1 ++ " ELSE " ++ pars !! 2 ++ " FI"
                    (view -> Vdivide _ _)             -> "(" ++ head pars ++ "/" ++ pars !! 1 ++ ")"
                    (view -> Vmodulo _ _)             -> "(" ++ head pars ++ "%" ++ pars !! 1 ++ ")"
                    (view -> Vgez _)                  -> "(" ++ head pars ++ ">=0)"
                    (view -> Vsum _)                  -> "(" ++ List.intercalate "+" (map (showMultElem "*") subExps) ++ ")"
                    (view -> Vproduct _)              -> "(" ++ List.intercalate "*" (map (showMultElem "^") subExps) ++ ")"
                    (view -> Vequal _ _)              -> "(" ++ head pars ++ "==" ++ pars !! 1 ++ ")"
                    (view -> Vand _)                  -> "(" ++ List.intercalate " /\\ " pars ++ ")"
                    (view -> Vnot _)                  -> "not(" ++ head pars ++ ")"
                    (view -> Vlength _)               -> "length(" ++ head pars ++ ")"
                    (view -> Vat _ _)                 -> "at(" ++ head pars ++ ", " ++ pars !! 1 ++ ")"
                    (view -> Vconcat _)               -> List.intercalate ":" pars
                    (view -> Vstrinre _ _)            -> "strinre(" ++ head pars ++ ", " ++ pars !! 1 ++ ")"
                    (view -> Vpredef _ fid _)         -> showFuncId f fid ++ "(" ++ List.intercalate ", " pars ++ ")"
                    _                                 -> error ("ShowValExprInContext.showVisitor not defined for " ++ show expr ++ "!")
        in ValExprVisitorOutput expr 1 str
    -- showVisitor
    
    showMultElem :: String -> ValExprVisitorOutput String -> String
    showMultElem op subExp =
        let mult = multiplicity subExp in
          customData subExp ++ if mult /= 1 then op ++ "(" ++ show mult ++ ")" else ""
-- showValExprInContext

showVarId :: LPEContext -> VarId.VarId -> String
showVarId f = mapGet f . TxsDefs.IdVar

showChanId :: LPEContext -> ChanId.ChanId -> String
showChanId f = mapGet f . TxsDefs.IdChan

showFuncId :: LPEContext -> FuncId.FuncId -> String
showFuncId f fid = Maybe.fromMaybe (Text.unpack (FuncId.name fid)) (f Map.!? TxsDefs.IdFunc fid)

showAccessorId :: LPEContext -> CstrId.CstrId -> Text.Text -> String
showAccessorId f cid n =
    case [ s | (TxsDefs.IdFunc fid, s) <- Map.toList f, FuncId.funcargs fid == [CstrId.cstrsort cid], FuncId.name fid == n ] of
      x:_ -> x
      [] -> error ("ShowValExprInContext.showVisitor has not been given a name for accessor \"" ++ Text.unpack n ++ "\"!")
-- showAccId

showSortId :: LPEContext -> SortId.SortId -> String
showSortId f sid = Maybe.fromMaybe (Text.unpack (SortId.name sid)) (f Map.!? TxsDefs.IdSort sid)



