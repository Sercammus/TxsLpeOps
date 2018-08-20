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
defaultValExprVisitor,
visitValExpr,
visitValExprM
) where

import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified FreeMonoidX as FMX
import qualified TxsDefs
import VarId
import ValExpr
import FuncDef
import FuncId

defaultValExprVisitor :: TxsDefs.VExpr -> Maybe TxsDefs.VExpr
defaultValExprVisitor _ = Nothing

visitValExpr :: (TxsDefs.VExpr -> Maybe TxsDefs.VExpr) -> TxsDefs.VExpr -> TxsDefs.VExpr
visitValExpr f expr@(view -> Vconst _) =
    case f expr of
      Just result -> result
      Nothing -> expr
visitValExpr f expr@(view -> Vvar _) =
    case f expr of
      Just result -> result
      Nothing -> expr
visitValExpr f expr@(view -> Vfunc fid vexps) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitValExpr f) vexps in cstrFunc emptyFis fid newVExps
visitValExpr f expr@(view -> Vcstr cid vexps) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitValExpr f) vexps in cstrCstr cid newVExps
visitValExpr f expr@(view -> Viscstr cid vexp) =
    case f expr of
      Just result -> result
      Nothing -> let newVExp = (visitValExpr f) vexp in cstrIsCstr cid newVExp
visitValExpr f expr@(view -> Vaccess cid p vexp) =
    case f expr of
      Just result -> result
      Nothing -> let newVExp = (visitValExpr f) vexp in cstrAccess cid p newVExp
visitValExpr f expr@(view -> Vite cond vexp1 vexp2) =
    case f expr of
      Just result -> result
      Nothing -> cstrITE (visitValExpr f cond) (visitValExpr f vexp1) (visitValExpr f vexp2)
visitValExpr f expr@(view -> Vdivide t n) =
    case f expr of
      Just result -> result
      Nothing -> cstrDivide (visitValExpr f t) (visitValExpr f n)
visitValExpr f expr@(view -> Vmodulo t n) =
    case f expr of
      Just result -> result
      Nothing -> cstrModulo (visitValExpr f t) (visitValExpr f n)
visitValExpr f expr@(view -> Vgez v) =
    case f expr of
      Just result -> result
      Nothing -> cstrGEZ (visitValExpr f v)
visitValExpr f expr@(view -> Vsum s) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitcOccur f) (FMX.toDistinctAscOccurListT s) in cstrSum (FMX.fromOccurListT newVExps)
visitValExpr f expr@(view -> Vproduct p) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitcOccur f) (FMX.toDistinctAscOccurListT p) in cstrProduct (FMX.fromOccurListT newVExps)
visitValExpr f expr@(view -> Vequal vexp1 vexp2) =
    case f expr of
      Just result -> result
      Nothing -> cstrEqual (visitValExpr f vexp1) (visitValExpr f vexp2)
visitValExpr f expr@(view -> Vand vexps) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitValExpr f) (Set.toList vexps) in cstrAnd (Set.fromList newVExps)
visitValExpr f expr@(view -> Vnot vexp) =
    case f expr of
      Just result -> result
      Nothing -> cstrNot (visitValExpr f vexp)
visitValExpr f expr@(view -> Vlength vexp) =
    case f expr of
      Just result -> result
      Nothing -> cstrLength (visitValExpr f vexp)
visitValExpr f expr@(view -> Vat s p) =
    case f expr of
      Just result -> result
      Nothing -> cstrAt (visitValExpr f s) (visitValExpr f p)
visitValExpr f expr@(view -> Vconcat vexps) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitValExpr f) vexps in cstrConcat newVExps
visitValExpr f expr@(view -> Vstrinre s r) =
    case f expr of
      Just result -> result
      Nothing -> cstrStrInRe (visitValExpr f s) (visitValExpr f r)
visitValExpr f expr@(view -> Vpredef kd fid vexps) =
    case f expr of
      Just result -> result
      Nothing -> let newVExps = map (visitValExpr f) vexps in cstrPredef kd fid newVExps
visitValExpr _ expr = error ("visitValExpr not defined for " ++ (show expr))
-- visitValExpr

visitcOccur :: (TxsDefs.VExpr -> Maybe TxsDefs.VExpr) -> (TxsDefs.VExpr, Integer) -> (TxsDefs.VExpr, Integer)
visitcOccur f (v, i) = (visitValExpr f v, i)

visitValExprM :: (TxsDefs.VExpr -> IOC.IOC (Maybe TxsDefs.VExpr)) -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
visitValExprM f expr@(view -> Vconst _) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do return expr
visitValExprM f expr@(view -> Vvar _) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do return expr
visitValExprM f expr@(view -> Vfunc fid vexps) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitValExprM f) vexps
                    return $ cstrFunc emptyFis fid newVExps
visitValExprM f expr@(view -> Vcstr cid vexps) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitValExprM f) vexps
                    return $ cstrCstr cid newVExps
visitValExprM f expr@(view -> Viscstr cid vexp) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExp <- visitValExprM f vexp
                    return $ cstrIsCstr cid newVExp
visitValExprM f expr@(view -> Vaccess cid p vexp) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExp <- visitValExprM f vexp
                    return $ cstrAccess cid p newVExp
visitValExprM f expr@(view -> Vite cond vexp1 vexp2) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newCond <- visitValExprM f cond
                    newVExp1 <- visitValExprM f vexp1
                    newVExp2 <- visitValExprM f vexp2
                    return $ cstrITE newCond newVExp1 newVExp2
visitValExprM f expr@(view -> Vdivide t n) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newT <- visitValExprM f t
                    newN <- visitValExprM f n
                    return $ cstrDivide newT newN
visitValExprM f expr@(view -> Vmodulo t n) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newT <- visitValExprM f t
                    newN <- visitValExprM f n
                    return $ cstrModulo newT newN
visitValExprM f expr@(view -> Vgez v) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newV <- visitValExprM f v
                    return $ cstrGEZ newV
visitValExprM f expr@(view -> Vsum s) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitcOccurM f) (FMX.toDistinctAscOccurListT s)
                    return $ cstrSum (FMX.fromOccurListT newVExps)
visitValExprM f expr@(view -> Vproduct p) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitcOccurM f) (FMX.toDistinctAscOccurListT p)
                    return $ cstrProduct (FMX.fromOccurListT newVExps)
visitValExprM f expr@(view -> Vequal vexp1 vexp2) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newExp1 <- visitValExprM f vexp1
                    newExp2 <- visitValExprM f vexp2
                    return $ cstrEqual newExp1 newExp2
visitValExprM f expr@(view -> Vand vexps) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitValExprM f) (Set.toList vexps)
                    return $ cstrAnd (Set.fromList newVExps)
visitValExprM f expr@(view -> Vnot vexp) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExp <- visitValExprM f vexp
                    return $ cstrNot newVExp
visitValExprM f expr@(view -> Vlength vexp) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExp <- visitValExprM f vexp
                    return $ cstrLength newVExp
visitValExprM f expr@(view -> Vat s p) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newS <- visitValExprM f s
                    newP <- visitValExprM f p
                    return $ cstrAt newS newP
visitValExprM f expr@(view -> Vconcat vexps) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitValExprM f) vexps
                    return $ cstrConcat newVExps
visitValExprM f expr@(view -> Vstrinre s r) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newS <- visitValExprM f s
                    newR <- visitValExprM f r
                    return $ cstrStrInRe newS newR
visitValExprM f expr@(view -> Vpredef kd fid vexps) = do
    maybeFExpr <- f expr
    case maybeFExpr of
      Just result -> do return result
      Nothing -> do newVExps <- mapM (visitValExprM f) vexps
                    return $ cstrPredef kd fid newVExps
visitValExprM _ expr = do error ("visitValExprM not defined for " ++ (show expr))
-- visitValExprM

visitcOccurM :: (TxsDefs.VExpr -> IOC.IOC (Maybe TxsDefs.VExpr)) -> (TxsDefs.VExpr, Integer) -> IOC.IOC (TxsDefs.VExpr, Integer)
visitcOccurM f (v, i) = do newVExp <- visitValExprM f v
                           return (newVExp, i)
-- visitcOccurM

emptyFis :: Map.Map FuncId (FuncDef VarId)
emptyFis = Map.empty :: Map.Map FuncId (FuncDef VarId)

