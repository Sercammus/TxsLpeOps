{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPESuccessors
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPESuccessors (
getPossibleSuccessors,
getDefiniteSuccessors
) where

import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           ValExpr

-- Selects all potential successors summands of a given summand from a list with all summands.
-- (In actuality, an overapproximation of all potential successors is selected, namely those
-- whose guard can be satisfied after the guard of the current summand has been satisfied and
-- after the substitutions of the process recursion have taken place.)
getPossibleSuccessors :: [LPESummand] -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossibleSuccessors _ _ (LPESummand _ _ _ LPEStop) = do return []
getPossibleSuccessors allSummands invariant (LPESummand _channelVars _channelOffers guard (LPEProcInst paramEqs)) = do
    immediateSuccessors <- Monad.foldM addSummandIfPossibleSuccessor [] allSummands
    return $ immediateSuccessors
  where
    addSummandIfPossibleSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfPossibleSuccessor soFar summand@(LPESummand _ _ g _) = do
      sat <- isSatisfiable (cstrAnd (Set.fromList [invariant, guard, varSubst paramEqs g]))
      return $ if sat then soFar ++ [summand] else soFar
-- getPossibleSuccessors

-- Selects all summands from a given list that are definitely successors of a given summand.
-- The result is an underapproximation!
getDefiniteSuccessors :: [LPESummand] -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getDefiniteSuccessors _ _ (LPESummand _ _ _ LPEStop) = do return []
getDefiniteSuccessors allSummands invariant (LPESummand _channelVars _channelOffers guard (LPEProcInst paramEqs)) = do
    immediateSuccessors <- Monad.foldM addSummandIfDefiniteSuccessor [] allSummands
    return $ immediateSuccessors
  where
    addSummandIfDefiniteSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfDefiniteSuccessor soFar summand@(LPESummand _ _ g _) = do
      taut <- isTautology (cstrAnd (Set.fromList [invariant, guard, varSubst paramEqs g]))
      return $ if taut then soFar ++ [summand] else soFar
-- getDefiniteSuccessors

