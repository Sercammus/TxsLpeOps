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
restoreTdefs,
eliminateAny,
doBlindSubst,
doBlindParamEqSubst,
doBlindParamEqsSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
-- import qualified EnvData
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified SortOf
import Constant hiding (sort)
import VarId
import ValExpr hiding (subst)
import ValExprVisitor
import VarFactory

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
eliminateAny :: TxsDefs.VExpr -> IOC.IOC (TxsDefs.TxsDefs, TxsDefs.VExpr, Set.Set VarId)
eliminateAny expr = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    visitorOutput <- visitValExprM eliminateAnyVisitorM expr
    return (tdefs, expression visitorOutput, customData visitorOutput)
  where
    eliminateAnyVisitorM :: [ValExprVisitorOutput (Set.Set VarId)] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput (Set.Set VarId))
    eliminateAnyVisitorM _ (view -> Vconst (Cany sort)) = do
        do varId <- createFreshVar sort
           return (ValExprVisitorOutput (cstrVar varId) 1 (Set.singleton varId))
    eliminateAnyVisitorM xs x = do
        vo <- MonadState.liftIO $ tryDefaultValExprVisitor (Set.unions (map customData xs)) xs x
        case vo of
          Left _ -> do -- IOC.putMsgs [ EnvData.TXS_CORE_ANY "Error found and caught (eliminateAny)!" ]
                       varId <- createFreshVar (SortOf.sortOf x)
                       return (ValExprVisitorOutput (cstrVar varId) 1 (Set.singleton varId))
          Right r -> return r
-- eliminateAny

-- Applies a substitution to the given expression, introducing 'undefined variables' (as defined above) where necessary.
-- Also returns the previous TorXakis definitions (so that they can be restored afterwards):
doBlindSubst :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
doBlindSubst subst expr = do
    visitorOutput <- visitValExprM substVisitor expr
    return (expression visitorOutput)
  where
    substVisitor :: [ValExprVisitorOutput ()] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput ())
    -- If we find a variable, substitute it (only if it is present in substEqs, of course):
    substVisitor _ (view -> Vvar varId) = do
        case Map.lookup varId subst of
          Just v -> do return (ValExprVisitorOutput v 1 ())
          Nothing -> do return (ValExprVisitorOutput (cstrVar varId) 1 ())
    -- In other cases, the parent expression inherits undefined variables from its sub-expressions.
    -- However, reconstruction of the parent expression might fail (because something was substituted incorrectly),
    -- in which case we return 'ANY <sort>' instead:
    substVisitor subExps parentExpr = do
        vo <- MonadState.liftIO $ tryDefaultValExprVisitor () subExps parentExpr
        case vo of
          Left _ -> do -- IOC.putMsgs [ EnvData.TXS_CORE_ANY "Error found and caught (doBlindSubst)!" ]
                       return (ValExprVisitorOutput (cstrConst (Cany (SortOf.sortOf parentExpr))) 1 ())
          Right r -> return r
      -- where
        -- handler :: Exception.SomeException -> IO (ValExprVisitorOutput ())
        -- handler _ = do return (ValExprVisitorOutput (cstrConst (Cany (SortOf.sortOf parentExpr))) 1 ())
-- doBlindSubst

-- Convenience method:
doBlindParamEqSubst :: Map.Map VarId TxsDefs.VExpr -> (VarId, TxsDefs.VExpr) -> IOC.IOC (VarId, TxsDefs.VExpr)
doBlindParamEqSubst subst (varId, expr) = do
    expr' <- doBlindSubst subst expr
    return (varId, expr')
-- doBlindParamEqSubst

doBlindParamEqsSubst :: Map.Map VarId TxsDefs.VExpr -> Map.Map VarId TxsDefs.VExpr -> IOC.IOC (Map.Map VarId TxsDefs.VExpr)
doBlindParamEqsSubst subst target = do
    paramEqs <- Monad.mapM (doBlindParamEqSubst subst) (Map.toList target)
    return (Map.fromList paramEqs)
-- doBlindParamEqsSubst

