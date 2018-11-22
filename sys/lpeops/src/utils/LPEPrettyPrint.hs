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
showAbbrevLPEInstance,
showLPESummand,
showAbbrevLPESummand,
showSubst,
showValExpr,
showAbbrevValExpr,
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified FuncId
import qualified CstrId
import qualified SortId
import qualified ChanId
import qualified FreeVar
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           VarId
import           LPETypeDefs
import           ValExprVisitor

type VarContext = Map.Map VarId String

createDefaultContextFromVarList :: [VarId] -> VarContext
createDefaultContextFromVarList = createDefaultContextFromVars . Set.fromList

createDefaultContextFromVars :: Set.Set VarId -> VarContext
createDefaultContextFromVars = Map.fromSet (Text.unpack . VarId.name)

createAbbrevContextFromVarList :: String -> [VarId] -> VarContext
createAbbrevContextFromVarList prefix vars = Map.fromList (map (\(v, n) -> (v, prefix ++ show (n::Integer))) (zip vars [1..]))

createAbbrevContextFromVars :: String -> Set.Set VarId -> VarContext
createAbbrevContextFromVars prefix = createAbbrevContextFromVarList prefix . Set.toList

getLPEInstanceAbbrevContext :: LPEInstance -> VarContext
getLPEInstanceAbbrevContext lpe@(_, initParamEqs, _) =
    let lpeParams = Map.keysSet initParamEqs in
    let lpeVars = getLPEInstanceVariables lpe Set.\\ lpeParams in
      Map.union (createAbbrevContextFromVars "par" lpeParams) (createAbbrevContextFromVars "var" lpeVars)
-- getLPEInstanceContext

getLPESummandAbbrevContext :: LPESummand -> VarContext
getLPESummandAbbrevContext summand = createAbbrevContextFromVars "var" (getLPESummandVariables summand)

-- Lists all variables that occur in an LPE:
getLPEInstanceVariables :: LPEInstance -> Set.Set VarId
getLPEInstanceVariables (_, initParamEqs, summands) =
    Set.union (getParamEqsVariables initParamEqs) (Set.unions (map getLPESummandVariables (Set.toList summands)))
-- getLPEInstanceVariables

getLPESummandVariables :: LPESummand -> Set.Set VarId
getLPESummandVariables (LPESummand channelVars channelOffers guard paramEqs) =
    Set.unions ([Set.fromList channelVars, Set.fromList (FreeVar.freeVars guard), getParamEqsVariables paramEqs] ++ map (Set.fromList . snd) channelOffers)
-- getLPESummandVariables

getParamEqsVariables :: LPEParamEqs -> Set.Set VarId
getParamEqsVariables eqs = Set.union (Map.keysSet eqs) (Set.unions (map (Set.fromList . FreeVar.freeVars) (Map.elems eqs)))

-- Shows an LPE in the default 'context'; that is,
-- variables are displayed using their actual names:
showLPEInstance :: LPEInstance -> String
showLPEInstance lpe = showLPEInstanceInContext (createDefaultContextFromVars (getLPEInstanceVariables lpe)) lpe

-- Shows an LPE in a 'free context'; that is,
-- fresh (short) names are introduces for each unique variable, and those names are used to display them:
showAbbrevLPEInstance :: LPEInstance -> String
showAbbrevLPEInstance lpe = showLPEInstanceInContext (getLPEInstanceAbbrevContext lpe) lpe

-- Shows an LPE in the specified 'context'; that is,
-- using specific names for specific variables when they occur:
showLPEInstanceInContext :: VarContext -> LPEInstance -> String
showLPEInstanceInContext f (chanIds, initParamEqs, summands) =
    "LPE[" ++ List.intercalate "; " (map showChanDecl chanIds) ++ "] (" ++
    showParamEqs initParamEqs ++ ") ::=\n        " ++
    List.intercalate "\n     ## " (map (showLPESummandInContext f) (Set.toList summands)) ++ "\n;"
  where
    showChanDecl :: ChanId.ChanId -> String
    showChanDecl chanId =
        let chanSortStrings = map (Text.unpack . SortId.name) (ChanId.chansorts chanId) in
          Text.unpack (ChanId.name chanId) ++ " :: " ++ List.intercalate " # " chanSortStrings
    -- showChanDecl
    
    showParamEqs :: LPEParamEqs -> String
    showParamEqs paramEqs = List.intercalate ", " (map showParamEq (Map.toList paramEqs))
    
    showParamEq :: (VarId, TxsDefs.VExpr) -> String
    showParamEq (varId, expr) = Text.unpack (VarId.name varId) ++ " = " ++ showValExprInContext f expr
-- showLPEInstanceInContext

-- Shows a summand in the default 'context'; that is,
-- variables are displayed using their actual names:
showLPESummand :: LPESummand -> String
showLPESummand summand = showLPESummandInContext (createDefaultContextFromVars (getLPESummandVariables summand)) summand

-- Shows a summand in a 'free context'; that is,
-- fresh (short) names are introduces for each unique variable, and those names are used to display them:
showAbbrevLPESummand :: LPESummand -> String
showAbbrevLPESummand summand = showLPESummandInContext (getLPESummandAbbrevContext summand) summand

-- Shows a summand in the specified 'context'; that is,
-- using specific names for specific variables when they occur:
showLPESummandInContext :: VarContext -> LPESummand -> String
showLPESummandInContext f (LPESummand channelVars channelOffers guard paramEqs) =
    let usedChannelVars = concatMap snd channelOffers in
    let hiddenChannelVars = Set.toList (Set.fromList channelVars Set.\\ Set.fromList usedChannelVars) in
      showChannelOffers channelOffers ++
      showHiddenVars hiddenChannelVars ++
      "[[ " ++ showValExprInContext f guard ++ " ]] >-> LPE(" ++ showParamEqs paramEqs ++ ")"
  where
    showChannelOffers :: LPEChannelOffers -> String
    showChannelOffers [] = ""
    showChannelOffers offers = List.intercalate " | " (map showChannelOffer offers) ++ " "
    
    showChannelOffer :: LPEChannelOffer -> String
    showChannelOffer (chanId, vars) = Text.unpack (ChanId.name chanId) ++ concatMap (\v -> " ? " ++ f Map.! v) vars
    
    showHiddenVars :: [VarId] -> String
    showHiddenVars [] = ""
    showHiddenVars hiddenVars = "(" ++ List.intercalate ", " (map (f Map.!) hiddenVars) ++ ") "
    
    showParamEqs :: LPEParamEqs -> String
    showParamEqs eqs = List.intercalate ", " (map showParamEq (Map.toList eqs))
    
    showParamEq :: (VarId, TxsDefs.VExpr) -> String
    showParamEq (varId, expr) = f Map.! varId ++ " = " ++ showValExprInContext f expr
-- showLPESummandInContext

-- Shows the given expression in the default 'context'; that is,
-- variables are displayed using their actual names:
showValExpr :: TxsDefs.VExpr -> String
showValExpr expr = showValExprInContext (createDefaultContextFromVarList (FreeVar.freeVars expr)) expr

-- Shows the given expression in a 'free context'; that is,
-- fresh (short) names are introduces for each unique variable, and those names are used to display them:
showAbbrevValExpr :: TxsDefs.VExpr -> String
showAbbrevValExpr expr =
    showValExprInContext (createAbbrevContextFromVarList "var" (FreeVar.freeVars expr)) expr
-- showAbbrevValExpr

-- Shows a substitution:
showSubst :: Map.Map VarId TxsDefs.VExpr -> String
showSubst subst = "[" ++ List.intercalate ", " (map (\(p, v) -> Text.unpack (VarId.name p) ++ " := " ++ showValExpr v) (Map.toList subst)) ++ "]"

-- Shows the given expression in the specified 'context'; that is,
-- using specific names for specific variables when they occur:
showValExprInContext :: VarContext -> TxsDefs.VExpr -> String
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
                    (view -> Vvar vid)                -> f Map.! vid
                    (view -> Vfunc fid _)             -> Text.unpack (FuncId.name fid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vcstr cid _)             -> Text.unpack (CstrId.name cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Viscstr cid _)           -> "is" ++ Text.unpack (CstrId.name cid) ++ "(" ++ head pars ++ ")"
                    (view -> Vaccess cid p _)         -> Text.unpack (FuncId.name (CstrId.cstrargs cid !! p)) ++ "(" ++ head pars ++ ")"
                    (view -> Vite _ _ _)              -> "IF " ++ head pars ++ " THEN " ++ pars !! 1 ++ " ELSE " ++ pars !! 2 ++ " ENDIF"
                    (view -> Vdivide _ _)             -> "(" ++ head pars ++ "/" ++ pars !! 1 ++ ")"
                    (view -> Vmodulo _ _)             -> "(" ++ head pars ++ "%" ++ pars !! 1 ++ ")"
                    (view -> Vgez _)                  -> head pars ++ ">=0"
                    (view -> Vsum _)                  -> "(" ++ List.intercalate "+" pars ++ ")"
                    (view -> Vproduct _)              -> "(" ++ List.intercalate "*" pars ++ ")"
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
-- showValExprInContext


