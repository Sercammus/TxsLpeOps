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
    let (valid, result) = visitValExpr validityVisitor expr in
      if valid
      then result
      else cstrConst (Cbool False)
  where
    -- The first element of the pair is the condition under which the second element is a DEFINED value.
    -- We abbreviate this with dc, for 'defined condition'.
    validityVisitor :: [(Bool, TxsDefs.VExpr)] -> TxsDefs.VExpr -> (Bool, TxsDefs.VExpr)
    validityVisitor _ (view -> Vvar varId) =
         -- Perform the substitution:
        case [v | (p, v) <- substEqs, p == varId] of
          [v] -> (True, v)
          _ -> (True, cstrVar varId)
    validityVisitor [(valid, cstrExpr@(view -> Vconst (Cstr c2 _fields)))] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if c1 == c2
        then (valid, cstrAccess c1 p cstrExpr)
        else (False, cstrConst (Cany (CstrId.cstrsort c1)))
    validityVisitor [(valid, cstrExpr@(view -> Vcstr c2 _fields))] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if (c1 == c2)
        then (valid, cstrAccess c1 p cstrExpr)
        else (False, cstrConst (Cany (CstrId.cstrsort c1)))
    validityVisitor vexps parentExpr =
        -- Usually, the parent expression is unsatisfiable if the children are unsatisfiable:
        (combineValidity vexps, defaultValExprVisitor (map snd vexps) parentExpr)
    -- validityVisitor
    
    combineValidity :: [(Bool, TxsDefs.VExpr)] -> Bool
    combineValidity [] = True
    combineValidity [(valid, _)] = valid
    combineValidity ((valid, _):xs) = valid && (combineValidity xs)
-- varSubst



