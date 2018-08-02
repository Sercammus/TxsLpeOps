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
visitValExpr
) where

import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified FreeMonoidX as FMX
import VarId
import ValExpr
import Variable
import FuncDef
import FuncId

-- Visits all sub-expressions of a (data) expression, and applies a function to them.
visitValExpr :: (Variable v)
             => (ValExpr v -> IOC.IOC (ValExpr v))  -- Function applied to every visited sub-expression.
             -> ValExpr v                           -- Current expression.
             -> IOC.IOC (ValExpr v)                 -- New expression.
visitValExpr f expr@(view -> Vconst _)               = do f $ expr
visitValExpr f expr@(view -> Vvar _)                 = do f $ expr
visitValExpr f      (view -> Vfunc fid vexps)        = do newVExps <- mapM (visitValExpr f) vexps
                                                          f $ cstrFunc emptyFis fid newVExps
visitValExpr f      (view -> Vcstr cid vexps)        = do newVExps <- mapM (visitValExpr f) vexps
                                                          f $ cstrCstr cid newVExps
visitValExpr f      (view -> Viscstr cid vexp)       = do newVExp <- visitValExpr f vexp
                                                          f $ cstrIsCstr cid newVExp
visitValExpr f      (view -> Vaccess cid p vexp)     = do newVExp <- visitValExpr f vexp
                                                          f $ cstrAccess cid p newVExp
visitValExpr f      (view -> Vite cond vexp1 vexp2)  = do newCond <- visitValExpr f cond
                                                          newVExp1 <- visitValExpr f vexp1
                                                          newVExp2 <- visitValExpr f vexp2
                                                          f $ cstrITE newCond newVExp1 newVExp2
visitValExpr f      (view -> Vdivide t n)            = do newT <- visitValExpr f t
                                                          newN <- visitValExpr f n
                                                          f $ cstrDivide newT newN
visitValExpr f      (view -> Vmodulo t n)            = do newT <- visitValExpr f t
                                                          newN <- visitValExpr f n
                                                          f $ cstrModulo newT newN
visitValExpr f      (view -> Vgez v)                 = do newV <- visitValExpr f v
                                                          f $ cstrGEZ newV
visitValExpr f      (view -> Vsum s)                 = do newVExps <- mapM (visitcOccur f) (FMX.toDistinctAscOccurListT s)
                                                          f $ cstrSum (FMX.fromOccurListT newVExps)
visitValExpr f      (view -> Vproduct p)             = do newVExps <- mapM (visitcOccur f) (FMX.toDistinctAscOccurListT p)
                                                          f $ cstrProduct (FMX.fromOccurListT newVExps)
visitValExpr f      (view -> Vequal vexp1 vexp2)     = do newVExp1 <- visitValExpr f vexp1
                                                          newVExp2 <- visitValExpr f vexp2
                                                          f $ cstrEqual newVExp1 newVExp2
visitValExpr f      (view -> Vand vexps)             = do newVExps <- mapM (visitValExpr f) (Set.toList vexps)
                                                          f $ cstrAnd (Set.fromList newVExps)
visitValExpr f      (view -> Vnot vexp)              = do newVExp <- visitValExpr f vexp
                                                          f $ cstrNot newVExp
visitValExpr f      (view -> Vlength vexp)           = do newVExp <- visitValExpr f vexp
                                                          f $ cstrLength newVExp
visitValExpr f      (view -> Vat s p)                = do newS <- visitValExpr f s
                                                          newP <- visitValExpr f p
                                                          f $ cstrAt newS newP
visitValExpr f      (view -> Vconcat vexps)          = do newVExps <- mapM (visitValExpr f) vexps
                                                          f $ cstrConcat newVExps
visitValExpr f      (view -> Vstrinre s r)           = do newS <- visitValExpr f s
                                                          newR <- visitValExpr f r
                                                          f $ cstrStrInRe newS newR
visitValExpr f      (view -> Vpredef kd fid vexps)   = do newVExps <- mapM (visitValExpr f) vexps
                                                          f $ cstrPredef kd fid newVExps
visitValExpr _ expr                                  = do error ("ValExprVisitor not defined for " ++ (show expr))
-- visitValExpr

visitcOccur :: (Variable v) => (ValExpr v -> IOC.IOC (ValExpr v)) -> (ValExpr v, Integer) -> IOC.IOC (ValExpr v, Integer)
visitcOccur f (v, i) = do newVExp <- visitValExpr f v
                          return (newVExp, i)

emptyFis :: Map.Map FuncId (FuncDef VarId)
emptyFis = Map.empty :: Map.Map FuncId (FuncDef VarId)

