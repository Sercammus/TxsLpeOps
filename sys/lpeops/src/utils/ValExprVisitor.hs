{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ValExprVisitor
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
module ValExprVisitor (
visitValExpr,
defaultValExprVisitor,
defaultValExprVisitorM,
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified FreeMonoidX as FMX
import qualified TxsDefs
import VarId
import ValExpr
import FuncDef
import FuncId

-- Function that applies a visitor pattern to the given value expression.
-- Children are always evaluated before the parent, and the result is a composition
-- that is dependent on the evaluated children and the parent.
visitValExpr :: ([(t, Integer)] -> TxsDefs.VExpr -> t) -> TxsDefs.VExpr -> t
visitValExpr f expr@(view -> Vconst _) =
      f [] expr
visitValExpr f expr@(view -> Vvar _) =
      f [] expr
visitValExpr f expr@(view -> Vfunc _fid vexps) =
    let newVExps = map (visitValExpr' f) vexps in
      f newVExps expr
visitValExpr f expr@(view -> Vcstr _cid vexps) =
    let newVExps = map (visitValExpr' f) vexps in
      f newVExps expr
visitValExpr f expr@(view -> Viscstr _cid vexp) =
    let newVExp = visitValExpr' f vexp in
      f [newVExp] expr
visitValExpr f expr@(view -> Vaccess _cid _p vexp) =
    let newVExp = visitValExpr' f vexp in
      f [newVExp] expr
visitValExpr f expr@(view -> Vite cond vexp1 vexp2) =
    let newCond = visitValExpr' f cond in
    let newVExp1 = visitValExpr' f vexp1 in
    let newVExp2 = visitValExpr' f vexp2 in
      f [newCond, newVExp1, newVExp2] expr
visitValExpr f expr@(view -> Vdivide t n) =
    let newT = visitValExpr' f t in
    let newN = visitValExpr' f n in
      f [newT, newN] expr
visitValExpr f expr@(view -> Vmodulo t n) =
    let newT = visitValExpr' f t in
    let newN = visitValExpr' f n in
      f [newT, newN] expr
visitValExpr f expr@(view -> Vgez v) =
    let newV = visitValExpr' f v in
      f [newV] expr
visitValExpr f expr@(view -> Vsum s) =
    let newVExps = map (\(v, k) -> (visitValExpr f v, k)) (FMX.toDistinctAscOccurListT s) in
      f newVExps expr
visitValExpr f expr@(view -> Vproduct p) =
    let newVExps = map (\(v, k) -> (visitValExpr f v, k)) (FMX.toDistinctAscOccurListT p) in
      f newVExps expr
visitValExpr f expr@(view -> Vequal vexp1 vexp2) =
    let newVExp1 = visitValExpr' f vexp1 in
    let newVExp2 = visitValExpr' f vexp2 in
      f [newVExp1, newVExp2] expr
visitValExpr f expr@(view -> Vand vexps) =
    let newVExps = map (visitValExpr' f) (Set.toList vexps) in
      f newVExps expr
visitValExpr f expr@(view -> Vnot vexp) =
    let newVExp = visitValExpr' f vexp in
      f [newVExp] expr
visitValExpr f expr@(view -> Vlength vexp) =
    let newVExp = visitValExpr' f vexp in
      f [newVExp] expr
visitValExpr f expr@(view -> Vat s p) =
    let newS = visitValExpr' f s in
    let newP = visitValExpr' f p in
      f [newS, newP] expr
visitValExpr f expr@(view -> Vconcat vexps) =
    let newVExps = map (visitValExpr' f) vexps in
      f newVExps expr
visitValExpr f expr@(view -> Vstrinre s r) =
    let newS = visitValExpr' f s in
    let newR = visitValExpr' f r in
      f [newS, newR] expr
visitValExpr f expr@(view -> Vpredef _kd _fid vexps) =
    let newVExps = map (visitValExpr' f) vexps in
      f newVExps expr
visitValExpr _ expr = error ("visitValExpr not defined for " ++ (show expr))
-- visitValExpr

visitValExpr' :: ([(t, Integer)] -> TxsDefs.VExpr -> t) -> TxsDefs.VExpr -> (t, Integer)
visitValExpr' f expr = (visitValExpr f expr, 1)

defaultValExprVisitor :: [(TxsDefs.VExpr, Integer)] -> TxsDefs.VExpr -> TxsDefs.VExpr
defaultValExprVisitor _ expr@(view -> Vconst _) = expr
defaultValExprVisitor _ expr@(view -> Vvar _) = expr
defaultValExprVisitor vexps _expr@(view -> Vfunc fid _) = cstrFunc emptyFis fid (map fst vexps)
  where
      emptyFis :: Map.Map FuncId (FuncDef VarId)
      emptyFis = Map.empty :: Map.Map FuncId (FuncDef VarId)
defaultValExprVisitor vexps _expr@(view -> Vcstr cid _) = cstrCstr cid (map fst vexps)
defaultValExprVisitor [(vexp, _)] _expr@(view -> Viscstr cid _) = cstrIsCstr cid vexp
defaultValExprVisitor [(vexp, _)] _expr@(view -> Vaccess cid p _) = cstrAccess cid p vexp
defaultValExprVisitor [(cond, _), (vexp1, _), (vexp2, _)] _expr@(view -> Vite _ _ _) = cstrITE cond vexp1 vexp2
defaultValExprVisitor [(t, _), (n, _)] _expr@(view -> Vdivide _ _) = cstrDivide t n
defaultValExprVisitor [(t, _), (n, _)] _expr@(view -> Vmodulo _ _) = cstrModulo t n
defaultValExprVisitor [(v, _)] _expr@(view -> Vgez _) = cstrGEZ v
defaultValExprVisitor vexps _expr@(view -> Vsum _) = cstrSum (FMX.fromOccurListT vexps)
defaultValExprVisitor vexps _expr@(view -> Vproduct _) = cstrProduct (FMX.fromOccurListT vexps)
defaultValExprVisitor [(vexp1, _), (vexp2, _)] _expr@(view -> Vequal _ _) = cstrEqual vexp1 vexp2
defaultValExprVisitor vexps _expr@(view -> Vand _) = cstrAnd (Set.fromList (map fst vexps))
defaultValExprVisitor [(vexp, _)] _expr@(view -> Vnot _) = cstrNot vexp
defaultValExprVisitor [(vexp, _)] _expr@(view -> Vlength _) = cstrLength vexp
defaultValExprVisitor [(s, _), (p, _)] _expr@(view -> Vat _ _) = cstrAt s p
defaultValExprVisitor vexps _expr@(view -> Vconcat _) = cstrConcat (map fst vexps)
defaultValExprVisitor [(s, _), (r, _)] _expr@(view -> Vstrinre _ _) = cstrStrInRe s r
defaultValExprVisitor vexps _expr@(view -> Vpredef kd fid _) = cstrPredef kd fid (map fst vexps)
defaultValExprVisitor _ expr = error ("defaultValExprVisitor not defined for (" ++ (show expr) ++ ")")

defaultValExprVisitorM :: Monad m => [(m TxsDefs.VExpr, Integer)] -> TxsDefs.VExpr -> m TxsDefs.VExpr
defaultValExprVisitorM vexps expr = do
    vexps' <- unpackList vexps
    return (defaultValExprVisitor vexps' expr)
  where
    unpackList :: Monad m => [(m TxsDefs.VExpr, Integer)] -> m [(TxsDefs.VExpr, Integer)]
    unpackList [] = do return []
    unpackList ((x, k):xs) = do
        x' <- x
        xs' <- unpackList xs
        return ((x', k):xs')
-- defaultValExprVisitorM


