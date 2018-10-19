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
defaultValExprVisitor
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
visitValExpr :: ([(t, Integer)] -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> t) -> t -> t) -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> t) -> TxsDefs.VExpr -> t
visitValExpr f g h expr =
    let visitValExprFGH = visitValExprK f g h 1 in
    let expr' = h expr in
      case expr of
        (view -> Vconst _) ->
            f [] g h expr'
        (view -> Vvar _) ->
            f [] g h expr'
        (view -> Vfunc _fid vexps) ->
            let newVExps = map visitValExprFGH vexps in
              f newVExps g h expr'
        (view -> Vcstr _cid vexps) ->
            let newVExps = map visitValExprFGH vexps in
              f newVExps g h expr'
        (view -> Viscstr _cid vexp) ->
            let newVExp = visitValExprFGH vexp in
              f [newVExp] g h expr'
        (view -> Vaccess _cid _p vexp) ->
            let newVExp = visitValExprFGH vexp in
              f [newVExp] g h expr'
        (view -> Vite cond vexp1 vexp2) ->
            let newCond = visitValExprFGH cond in
            let newVExp1 = visitValExprFGH vexp1 in
            let newVExp2 = visitValExprFGH vexp2 in
              f [newCond, newVExp1, newVExp2] g h expr'
        (view -> Vdivide t n) ->
            let newT = visitValExprFGH t in
            let newN = visitValExprFGH n in
              f [newT, newN] g h expr'
        (view -> Vmodulo t n) ->
            let newT = visitValExprFGH t in
            let newN = visitValExprFGH n in
              f [newT, newN] g h expr'
        (view -> Vgez v) ->
            let newV = visitValExprFGH v in
              f [newV] g h expr'
        (view -> Vsum s) ->
            let newVExps = map (\(v, k) -> visitValExprK f g h k v) (FMX.toDistinctAscOccurListT s) in  
              f newVExps g h expr'
        (view -> Vsum s) ->
            let newVExps = map (\(v, k) -> visitValExprK f g h k v) (FMX.toDistinctAscOccurListT s) in
              f newVExps g h expr'
        (view -> Vproduct p) ->
            let newVExps = map (\(v, k) -> visitValExprK f g h k v) (FMX.toDistinctAscOccurListT p) in
              f newVExps g h expr'
        (view -> Vequal vexp1 vexp2) ->
            let newVExp1 = visitValExprFGH vexp1 in
            let newVExp2 = visitValExprFGH vexp2 in
              f [newVExp1, newVExp2] g h expr'
        (view -> Vand vexps) ->
            let newVExps = map visitValExprFGH (Set.toList vexps) in
              f newVExps g h expr'
        (view -> Vnot vexp) ->
            let newVExp = visitValExprFGH vexp in
              f [newVExp] g h expr'
        (view -> Vlength vexp) ->
            let newVExp = visitValExprFGH vexp in
              f [newVExp] g h expr'
        (view -> Vat s p) ->
            let newS = visitValExprFGH s in
            let newP = visitValExprFGH p in
              f [newS, newP] g h expr'
        (view -> Vconcat vexps) ->
            let newVExps = map visitValExprFGH vexps in
              f newVExps g h expr'
        (view -> Vstrinre s r) ->
            let newS = visitValExprFGH s in
            let newR = visitValExprFGH r in
              f [newS, newR] g h expr'
        (view -> Vpredef _kd _fid vexps) ->
            let newVExps = map visitValExprFGH vexps in
              f newVExps g h expr'
        _ -> error ("VisitValExpr not defined for " ++ (show expr) ++ "!")
-- visitValExpr

visitValExprK :: ([(t, Integer)] -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> t) -> t -> t) -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> t) -> Integer -> TxsDefs.VExpr -> (t, Integer)
visitValExprK f g h k expr = (visitValExpr f g h expr, k)

defaultValExprVisitor :: [(t, Integer)] -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> t) -> t -> t
defaultValExprVisitor subExps g h expr =
    let expr' = g expr in
    let gfst = g . fst in
      case expr' of
        (view -> Vconst _) -> h $ expr'
        (view -> Vvar _) -> h $ expr'
        (view -> Vfunc fid _) -> h $ cstrFunc emptyFis fid (map gfst subExps)
        (view -> Vcstr cid _) -> h $ cstrCstr cid (map gfst subExps)
        (view -> Viscstr cid _) -> h $ cstrIsCstr cid (gfst (subExps !! 0))
        (view -> Vaccess cid p _) -> h $ cstrAccess cid p (gfst (subExps !! 0))
        (view -> Vite{}) -> h $ cstrITE (gfst (subExps !! 0)) (gfst (subExps !! 1)) (gfst (subExps !! 2))
        (view -> Vdivide _ _) -> h $ cstrDivide (gfst (subExps !! 0)) (gfst (subExps !! 1))
        (view -> Vmodulo _ _) -> h $ cstrModulo (gfst (subExps !! 0)) (gfst (subExps !! 1))
        (view -> Vgez _) -> h $ cstrGEZ (gfst (subExps !! 0))
        (view -> Vsum _) -> h $ cstrSum (FMX.fromOccurListT (map (\(v, k) -> (g v, k)) subExps))
        (view -> Vproduct _) -> h $ cstrProduct (FMX.fromOccurListT (map (\(v, k) -> (g v, k)) subExps))
        (view -> Vequal _ _) -> h $ cstrEqual (gfst (subExps !! 0)) (gfst (subExps !! 1))
        (view -> Vand _) -> h $ cstrAnd (Set.fromList (map gfst subExps))
        (view -> Vnot _) -> h $ cstrNot (gfst (subExps !! 0))
        (view -> Vlength _) -> h $ cstrLength (gfst (subExps !! 0))
        (view -> Vat _ _) -> h $ cstrAt (gfst (subExps !! 0)) (gfst (subExps !! 1))
        (view -> Vconcat _) -> h $ cstrConcat (map gfst subExps)
        (view -> Vstrinre _ _) -> h $ cstrStrInRe (gfst (subExps !! 0)) (gfst (subExps !! 1))
        (view -> Vpredef kd fid _) -> h $ cstrPredef kd fid (map gfst subExps)
        otherExpr -> error ("DefaultValExprVisitor not defined for " ++ (show otherExpr) ++ "!")
  where
      emptyFis :: Map.Map FuncId (FuncDef VarId)
      emptyFis = Map.empty :: Map.Map FuncId (FuncDef VarId)
-- defaultValExprVisitor

