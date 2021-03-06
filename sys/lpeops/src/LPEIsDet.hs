{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEIsDet
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEIsDet (
isDeterministicLPE,
filterNonDeterministicSummands,
getPossibleCoActors
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Set as Set
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified ChanId
import qualified ValExpr
import LPEOps
import BlindSubst
import Satisfiability

-- Checks if the given LPE is deterministic.
-- The conclusion is printed to the console, and the input LPE is returned.
isDeterministicLPE :: LPEOperation
isDeterministicLPE (tdefs, mdef, lpe@(_, _, _, summands)) _out invariant = do
    nonDetSummands <- filterNonDeterministicSummands summands invariant
    if nonDetSummands == Set.empty
    then IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Model is deterministic!") ]
    else IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Model may be non-deterministic (found " ++ show (Set.size nonDetSummands) ++ " summands with possible overlap)!") ]
    return (Right (tdefs, mdef, lpe))
-- isDeterministicLPE

filterNonDeterministicSummands :: LPESummands -> TxsDefs.VExpr -> IOC.IOC LPESummands
filterNonDeterministicSummands allSummands invariant =
    Set.unions <$> Monad.mapM perSummand (Set.toList allSummands)
  where
    perSummand :: LPESummand -> IOC.IOC LPESummands
    perSummand summand = do
        coActors <- getPossibleCoActors (Set.delete summand allSummands) invariant summand
        if coActors /= Set.empty
        then return (Set.insert summand coActors)
        else return Set.empty
-- filterNonDeterministicSummands

-- Selects all summands from a given list that could generate the same action (both label and arguments)
-- at the same time (= in the same state) as a specified summand.
-- The result is an overapproximation!
getPossibleCoActors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC LPESummands
getPossibleCoActors allSummands invariant (LPESummand _ chans1 guard1 _) =
    Set.fromList <$> Monad.filterM isPossibleCoActor (Set.toList allSummands)
  where
    isPossibleCoActor :: LPESummand -> IOC.IOC Bool
    isPossibleCoActor (LPESummand _ chans2 guard2 _) = do
        let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
        let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
        -- All action labels must be the same (order does not matter, because we sorted):
        if map fst sortedChans1 /= map fst sortedChans2
        then return False
        else do -- Both guards must be able to be true at the same time:
                let guards = ValExpr.cstrAnd (Set.fromList [guard1, guard2])
                notSat <- isNotSatisfiable guards invariant
                if notSat
                then return False
                else do -- All action arguments must be able to have the same value.
                        -- To check this, substitute the (by definition fresh) channel variables of one summand into the other:
                        let chanVars1 = concatMap snd sortedChans1
                        let chanVars2 = concatMap snd sortedChans2
                        let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
                        guard2' <- doBlindSubst subst guard2
                        let guardEq = ValExpr.cstrEqual guard1 guard2'
                        isSatisfiable guardEq invariant
-- getPossibleCoActors

