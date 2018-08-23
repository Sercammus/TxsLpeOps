{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Satisfiability
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module VarFactory (
createFreshVar,
createFreshVarFromPrefix,
createVarSubst,
varSubst
) where

import qualified EnvCore as IOC
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified SortId
import qualified Id
import qualified TxsDefs
import ConstDefs hiding (sort)
import CstrId
import VarId
import ValExpr
import ValExprVisitor

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVar :: SortId.SortId -> IOC.IOC VarId.VarId
createFreshVar sort = do
    varUnid <- IOC.newUnid
    let idAsInt = Id._id varUnid
    let absId = if idAsInt >= 0 then idAsInt else -idAsInt
    return VarId.VarId { VarId.name = Text.pack ("__FV" ++ (show absId)), VarId.unid = varUnid, VarId.varsort = sort }
-- createVar

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVarFromPrefix :: String -> SortId.SortId -> IOC.IOC VarId.VarId
createFreshVarFromPrefix prefix sort = do
    varUnid <- IOC.newUnid
    let idAsInt = Id._id varUnid
    let absId = if idAsInt >= 0 then idAsInt else -idAsInt
    return VarId.VarId { VarId.name = Text.pack (prefix ++ (show absId)), VarId.unid = varUnid, VarId.varsort = sort }
-- createFreshVarFromPrefix

createVarSubst :: [(VarId, TxsDefs.VExpr)] -> (TxsDefs.VExpr -> TxsDefs.VExpr)
createVarSubst substEqs = (\e -> varSubst substEqs (e :: TxsDefs.VExpr))

varSubst :: [(VarId, TxsDefs.VExpr)] -> TxsDefs.VExpr -> TxsDefs.VExpr
varSubst substEqs expr =
    let (p, v) = visitValExpr substVisitor expr in vexpAnd p v
  where
    -- The first element of the pair is the condition under which the second element is a DEFINED value.
    -- We abbreviate this with dc, for 'defined condition'.
    substVisitor :: [(TxsDefs.VExpr, TxsDefs.VExpr)] -> TxsDefs.VExpr -> (TxsDefs.VExpr, TxsDefs.VExpr)
    substVisitor _ (view -> Vvar varId) =
         -- Perform the substitution:
        case [v | (p, v) <- substEqs, p == varId] of
          [v] -> (vexpTrue, v)
          _ -> (vexpTrue, cstrVar varId)
    substVisitor [(dc, cstrExpr@(view -> Vconst (Cstr c2 _fields)))] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if c1 == c2
        then (dc, cstrAccess c1 p cstrExpr)
        else (vexpFalse, cstrConst (Cany (CstrId.cstrsort c1)))
    substVisitor [(dc, cstrExpr@(view -> Vcstr c2 _fields))] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if (c1 == c2)
        then (dc, cstrAccess c1 p cstrExpr)
        else (vexpFalse, cstrConst (Cany (CstrId.cstrsort c1)))
    substVisitor [(validCond, cond), (validVExp1, vexp1), (validVExp2, vexp2)] (view -> Vite _ _ _) =
        let ifBranchCond = vexpAnd (vexpAnd validCond cond) (cstrNot validVExp1) in
        let elseBranchCond = vexpAnd (vexpOr (cstrNot validCond) (cstrNot cond)) validVExp2 in
          (vexpOr ifBranchCond elseBranchCond, cstrITE cond vexp1 vexp2)
    substVisitor vexps _expr@(view -> Vand _) =
        -- Just return false if one of the conjuncts is unsatisfiable:
        (combineValidity vexps, cstrAnd (Set.fromList (map snd vexps)))
    substVisitor [(dc, vexp)] _expr@(view -> Vnot _) =
        -- Just return true if the operand is unsatisfiable:
        (cstrNot dc, cstrNot vexp)
    substVisitor vexps parentExpr =
        -- Usually, the parent expression is unsatisfiable if the children are unsatisfiable:
        (combineValidity vexps, defaultValExprVisitor (map snd vexps) parentExpr)
    -- substVisitor
    
    combineValidity :: [(TxsDefs.VExpr, TxsDefs.VExpr)] -> TxsDefs.VExpr
    combineValidity [] = vexpTrue
    combineValidity vals = cstrAnd (Set.fromList (map fst vals))
    
    vexpAnd :: TxsDefs.VExpr -> TxsDefs.VExpr -> TxsDefs.VExpr
    vexpAnd lhs rhs = cstrAnd (Set.fromList [lhs, rhs])
    
    vexpOr :: TxsDefs.VExpr -> TxsDefs.VExpr -> TxsDefs.VExpr
    vexpOr lhs rhs = cstrNot (cstrAnd (Set.fromList [cstrNot lhs, cstrNot rhs]))
    
    vexpTrue :: TxsDefs.VExpr
    vexpTrue = cstrConst (Cbool True)
    
    vexpFalse :: TxsDefs.VExpr
    vexpFalse = cstrConst (Cbool False)
-- varSubst



