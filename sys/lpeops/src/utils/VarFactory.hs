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

module VarFactory (
createFreshVar,
createFreshVarFromPrefix,
varSubst
) where

import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified SortOf
import qualified Subst
import qualified SortId
import qualified Id
import qualified TxsDefs
import VarId
import ValExpr

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

-- Substitutes variables in the given expression in a safe manner; that is,
-- the expression does not cause accessors to be applied to inappropriate constructors.
varSubst :: [(VarId, TxsDefs.VExpr)] -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
varSubst substEqs expr = do
    let vars = map fst substEqs
    tempVars <- Monad.mapM createFreshVar (map SortOf.sortOf vars)
    let tempVarExprs = map cstrVar tempVars
    let newExpr = Subst.subst (Map.fromList (zip vars tempVarExprs)) Map.empty expr
    let conjuncts = zipWith cstrEqual tempVarExprs (map snd substEqs)
    return (cstrAnd (Set.fromList (newExpr:conjuncts)))
-- varSubst

