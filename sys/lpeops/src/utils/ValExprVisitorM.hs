{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ValExprVisitorM
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
module ValExprVisitorM (
visitValExprM,
defaultValExprVisitorM
) where

import qualified Control.Monad as Monad
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
visitValExprM :: Monad.Monad m => ([(t, Integer)] -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> m t) -> t -> m t) -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> m t) -> TxsDefs.VExpr -> m t
visitValExprM f g h expr = do
    let visitValExprMFGH = visitValExprMK f g h 1
    expr' <- h expr
    case expr of
      (view -> Vconst _) ->
          f [] g h expr'
      (view -> Vvar _) ->
          f [] g h expr'
      (view -> Vfunc _fid vexps) ->
          do newVExps <- Monad.mapM visitValExprMFGH vexps
             f newVExps g h expr'
      (view -> Vcstr _cid vexps) ->
          do newVExps <- Monad.mapM visitValExprMFGH vexps
             f newVExps g h expr'
      (view -> Viscstr _cid vexp) ->
          do newVExp <- visitValExprMFGH vexp
             f [newVExp] g h expr'
      (view -> Vaccess _cid _p vexp) ->
          do newVExp <- visitValExprMFGH vexp
             f [newVExp] g h expr'
      (view -> Vite cond vexp1 vexp2) ->
          do newCond <- visitValExprMFGH cond
             newVExp1 <- visitValExprMFGH vexp1
             newVExp2 <- visitValExprMFGH vexp2
             f [newCond, newVExp1, newVExp2] g h expr'
      (view -> Vdivide t n) ->
          do newT <-visitValExprMFGH t
             newN <- visitValExprMFGH n
             f [newT, newN] g h expr'
      (view -> Vmodulo t n) ->
          do newT <- visitValExprMFGH t
             newN <- visitValExprMFGH n
             f [newT, newN] g h expr'
      (view -> Vgez v) ->
          do newV <- visitValExprMFGH v
             f [newV] g h expr'
      (view -> Vsum s) ->
          do newVExps <- Monad.mapM (\(v, k) -> visitValExprMK f g h k v) (FMX.toDistinctAscOccurListT s)
             f newVExps g h expr'
      (view -> Vproduct p) ->
          do newVExps <- Monad.mapM (\(v, k) -> visitValExprMK f g h k v) (FMX.toDistinctAscOccurListT p)
             f newVExps g h expr'
      (view -> Vequal vexp1 vexp2) ->
          do newVExp1 <- visitValExprMFGH vexp1
             newVExp2 <- visitValExprMFGH vexp2
             f [newVExp1, newVExp2] g h expr'
      (view -> Vand vexps) ->
          do newVExps <- Monad.mapM visitValExprMFGH (Set.toList vexps)
             f newVExps g h expr'
      (view -> Vnot vexp) ->
          do newVExp <- visitValExprMFGH vexp
             f [newVExp] g h expr'
      (view -> Vlength vexp) ->
          do newVExp <- visitValExprMFGH vexp
             f [newVExp] g h expr'
      (view -> Vat s p) ->
          do newS <- visitValExprMFGH s
             newP <- visitValExprMFGH p
             f [newS, newP] g h expr'
      (view -> Vconcat vexps) ->
          do newVExps <- Monad.mapM visitValExprMFGH vexps
             f newVExps g h expr'
      (view -> Vstrinre s r) ->
          do newS <- visitValExprMFGH s
             newR <- visitValExprMFGH r
             f [newS, newR] g h expr'
      (view -> Vpredef _kd _fid vexps) ->
          do newVExps <- Monad.mapM visitValExprMFGH vexps
             f newVExps g h expr'
      _ -> error ("VisitValExprM not defined for " ++ (show expr) ++ "!")
-- visitValExprM

visitValExprMK :: Monad m => ([(t, Integer)] -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> m t) -> t -> m t) -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> m t) -> Integer -> TxsDefs.VExpr -> m (t, Integer)
visitValExprMK f g h k expr = do
    expr' <- visitValExprM f g h expr
    return (expr', k)
-- visitValExprMK

defaultValExprVisitorM :: Monad m => [(t, Integer)] -> (t -> TxsDefs.VExpr) -> (TxsDefs.VExpr -> m t) -> t -> m t
defaultValExprVisitorM subExps g h expr =
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
        otherExpr -> error ("DefaultValExprVisitorM not defined for " ++ (show otherExpr) ++ "!")
  where
      emptyFis :: Map.Map FuncId (FuncDef VarId)
      emptyFis = Map.empty :: Map.Map FuncId (FuncDef VarId)
-- defaultValExprVisitorM


