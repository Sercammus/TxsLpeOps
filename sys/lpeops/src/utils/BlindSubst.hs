{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  BlindSubst
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module BlindSubst (
BlindValExpr,
BlindSubstitution,
BlindSolution(..),
toBlindSubstitution,
toBlindSolution,
lookupBlindValExpr,
restoreTdefs,
eliminateAny,
doBlindSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified SolveDefs
import qualified SortOf
import Constant hiding (sort)
import VarId
import ValExpr hiding (subst)
import CstrId
import ValExprVisitor
import VarFactory

-- Doing substitutions in expressions may result in (partially) undefined expressions!
-- (In particular, imagine substituting a constructor in an incompatible field access function.)
-- To handle this, each expression carries additional information, namely
-- a list of 'undefined variables', which are variables that represent undefined sub-expressions:
type BlindValExpr = (TxsDefs.VExpr, Set.Set VarId)

type BlindSubstitution = Map.Map VarId BlindValExpr

data BlindSolution = Solution BlindSubstitution
                   | Unsolvable
                   | UnableToSolve
                   deriving (Eq, Show)
-- BlindSolution

toBlindSubstitution :: Map.Map VarId TxsDefs.VExpr -> BlindSubstitution
toBlindSubstitution subst = Map.map (\v -> (v, Set.empty)) subst

toBlindSolution :: SolveDefs.SolveProblem VarId -> BlindSolution
toBlindSolution (SolveDefs.Solved solMap) = Solution (Map.map (\c -> (cstrConst c, Set.empty)) solMap)
toBlindSolution SolveDefs.Unsolvable = Unsolvable
toBlindSolution SolveDefs.UnableToSolve = UnableToSolve

lookupBlindValExpr :: VarId -> BlindSubstitution -> BlindValExpr
lookupBlindValExpr varId m = Map.findWithDefault (cstrConst (Cany (SortOf.sortOf varId)), Set.empty) varId m

-- Manipulating expressions (e.g. blind substitutions before SAT-solving) may require helper variables.
-- These variables are added to the TorXakis definitions in the environment of the monad.
-- To undo these additions, pass the original definitions to the following helper method:
restoreTdefs :: TxsDefs.TxsDefs -> IOC.IOC ()
restoreTdefs tdefs = do
    state <- MonadState.gets IOC.state
    let newState = state { IOC.tdefs = tdefs }
    MonadState.modify (\env -> env { IOC.state = newState })
-- restoreTdefs

-- Eliminates occurrences of 'ANY <sort>' by substituting fresh, free variables.
-- Also returns the previous TorXakis definitions (so that they can be restored afterwards, see above).
eliminateAny :: BlindValExpr -> IOC.IOC (TxsDefs.TxsDefs, BlindValExpr)
eliminateAny (expr, undefs) = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    newExpr <- visitValExprM eliminateAnyVisitorM expr
    return (tdefs, (expression newExpr, Set.union undefs (customData newExpr)))
  where
    eliminateAnyVisitorM :: [ValExprVisitorOutput (Set.Set VarId)] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput (Set.Set VarId))
    eliminateAnyVisitorM _ (view -> Vconst (Cany sort)) = do
        do varId <- createFreshVar sort
           return (ValExprVisitorOutput (cstrVar varId) 1 (Set.singleton varId))
    eliminateAnyVisitorM xs x = defaultValExprVisitorM (Set.unions (map customData xs)) xs x
-- eliminateAny

-- Applies a substitution to the given expression, introducing 'undefined variables' (as defined above) where necessary.
-- Also returns the previous TorXakis definitions (so that they can be restored afterwards):
doBlindSubst :: BlindSubstitution -> BlindValExpr -> IOC.IOC (TxsDefs.TxsDefs, BlindValExpr)
doBlindSubst subst (expr, undefs) = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let substList = Map.toList subst
    newSubstListSnds <- Monad.mapM eliminateAny (map snd substList)
    let newSubst = Map.fromList (zip (map fst substList) (map snd newSubstListSnds))
    expr' <- visitValExprM (substVisitor newSubst) expr
    return (tdefs, (expression expr', Set.union undefs (customData expr')))
  where
    substVisitor :: BlindSubstitution -> [ValExprVisitorOutput (Set.Set VarId)] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput (Set.Set VarId))
    -- If we find a variable, substitute it (only if it is present in substEqs, of course):
    substVisitor bs _ (view -> Vvar varId) =
        case Map.lookup varId bs of
          Just (v, udefs) -> do return (ValExprVisitorOutput v 1 udefs)
          Nothing -> do return (ValExprVisitorOutput (cstrVar varId) 1 Set.empty)
    -- An expression that accesses a non-existent field (possible when using an accessor on the wrong constructor sort)
    -- means that we introduce a new 'undefined variable':
    substVisitor _ [(ValExprVisitorOutput (subExpr@(view -> Vcstr c1 _fields)) _ udefs)] (view -> Vaccess c2 p _vexp) =
        if c1 == c2
        then do return (ValExprVisitorOutput (cstrAccess c2 p subExpr) 1 udefs)
        else do varId <- createFreshVar ((CstrId.cstrargs c1) !! p)
                return (ValExprVisitorOutput (cstrVar varId) 1 (Set.insert varId udefs))
    -- Constructors exist in constant and non-constant forms.
    -- We do the same here as above, but for the constant form:
    substVisitor _ [(ValExprVisitorOutput (subExpr@(view -> Vconst (Ccstr c1 _fields))) _ udefs)] (view -> Vaccess c2 p _vexp) =
        if c1 == c2
        then do return (ValExprVisitorOutput (cstrAccess c2 p subExpr) 1 udefs)
        else do varId <- createFreshVar ((CstrId.cstrargs c1) !! p)
                return (ValExprVisitorOutput (cstrVar varId) 1 (Set.insert varId udefs))
    -- In other cases, the parent expression inherits undefined variables from its sub-expressions:
    substVisitor _ subExps parentExpr = do
        parentExpr' <- defaultValExprVisitorM Set.empty subExps parentExpr
        return (parentExpr' { customData = Set.unions (map customData subExps) })
-- doBlindSubst











