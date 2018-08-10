{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEConfCheck
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEConfCheck (
chanIdConfluentIstep,
confCheck,
confElm
) where

import qualified Control.Monad       as Monad
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified Subst
import           TxsDefs hiding (guard)
import           LPEOps
import           Satisfiability
import           VarId
import           ValExpr
import           ConstDefs

chanIdConfluentIstep :: ChanId
chanIdConfluentIstep = ChanId (Text.pack "CISTEP") 969 []

-- LPE rewrite method.
confCheck :: LPEOperation
confCheck (channels, paramEqs, summands) = do
    let tauSummands = filter isTauSummand summands
    confluentTauSummands <- Monad.filterM (isConfluentTauSummand summands) tauSummands
    let noConfluentTauSummands = (Set.fromList summands) Set.\\ (Set.fromList confluentTauSummands)
    let newSummands = Set.union noConfluentTauSummands (Set.fromList (map flagTauSummand confluentTauSummands))
    do return $ Just (channels, paramEqs, Set.toList newSummands)
-- confCheck

isTauSummand :: LPESummand -> Bool
isTauSummand (LPESummand [(chanId, _)] _ _) = chanId == chanIdIstep
isTauSummand _ = False
-- isTauSummand

flagTauSummand :: LPESummand -> LPESummand
flagTauSummand (LPESummand [(_chanId, commVars)] guard paramEqs) = (LPESummand [(chanIdConfluentIstep, commVars)] guard paramEqs)
flagTauSummand tauSummand = tauSummand

isFlaggedTauSummand :: LPESummand -> Bool
isFlaggedTauSummand (LPESummand [(chanId, _)] _ _) = chanId == chanIdConfluentIstep
isFlaggedTauSummand _ = False
-- isFlaggedTauSummand

isConfluentTauSummand :: [LPESummand] -> LPESummand -> IOC.IOC Bool
isConfluentTauSummand [] _ = do return True
isConfluentTauSummand (x:xs) tauSummand = do
    check <- checkConfluenceCondition tauSummand x
    if check
    then isConfluentTauSummand xs tauSummand
    else do return False
-- isConfluentTauSummand

checkConfluenceCondition :: LPESummand -> LPESummand -> IOC.IOC Bool
checkConfluenceCondition LPEStopSummand _ = do return False
checkConfluenceCondition _ LPEStopSummand = do return False
checkConfluenceCondition (LPESummand _channelOffers1 guard1 paramEqs1) (LPESummand channelOffers2 guard2 paramEqs2) = do
    let channelVars = Set.toList (foldl getChannelVars Set.empty channelOffers2)
    -- a1 == a1[g1] && ... && an == an[g1]
    let channelArgEqs = map (\varId -> cstrEqual (cstrVar varId) (g1 (cstrVar varId))) channelVars
    -- x1[g1][g2] == x1[g2][g1] && ... && xn[g1][g2] == xn[g2][g1]
    let instantiationEqs = map (\(p, _) -> cstrEqual (g1 (g2 (cstrVar p))) (g2 (g1 (cstrVar p)))) paramEqs2
    -- c1 && c2
    let premise = cstrAnd (Set.fromList [guard1, guard2])
    let conclusion = cstrAnd (Set.fromList ([g2 guard1, g1 guard2] ++ channelArgEqs ++ instantiationEqs))
    let confluenceCondition = cstrITE premise conclusion (cstrConst (Cbool True))
    inv <- isInvariant confluenceCondition
    return inv
  where
    getChannelVars :: Set.Set VarId -> LPEChannelOffer -> Set.Set VarId
    getChannelVars soFar (_chanId, commVars) = Set.union soFar (Set.fromList commVars)
    
    g1 = \e -> Subst.subst (Map.fromList paramEqs1) Map.empty (e :: TxsDefs.VExpr)
    g2 = \e -> Subst.subst (Map.fromList paramEqs2) Map.empty (e :: TxsDefs.VExpr)
-- checkConfluenceCondition

-- LPE rewrite method.
confElm :: LPEOperation
confElm lpeInstance = do
    maybeLpeInstance <- confCheck lpeInstance
    case maybeLpeInstance of
      Just (channels, paramEqs, summands) -> do definiteSuccessors <- Monad.mapM (getDefiniteSuccessors summands) summands
                                                return $ Just (channels, paramEqs, zipWith mergeSummands summands definiteSuccessors)
      _ -> do return Nothing
  where
    mergeSummands :: LPESummand -> [LPESummand] -> LPESummand
    mergeSummands summand@(LPESummand chans g eqs1) successors =
        case [ suc | suc <- successors, isFlaggedTauSummand suc ] of
          [LPESummand _ _ eqs2] ->
            let substitution = \e -> Subst.subst (Map.fromList eqs1) Map.empty (e :: TxsDefs.VExpr) in
              LPESummand chans g [ (p, substitution v) | (p, v) <- eqs2 ]
          _ -> summand
    mergeSummands summand _ = summand
-- confElm

-- Selects all potential successors summands of a given summand from a list with all summands.
-- (In actuality, an overapproximation of all potential successors is selected, namely those
-- whose guard can be satisfied after the guard of the current summand has been satisfied and
-- after the substitutions of the process recursion have taken place.)
getDefiniteSuccessors :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
getDefiniteSuccessors _ LPEStopSummand = do return []
getDefiniteSuccessors allSummands (LPESummand _channelOffers guard paramEqs) = do
    immediateSuccessors <- Monad.foldM addSummandIfImmediateSuccessor [] allSummands
    return $ immediateSuccessors
  where
    addSummandIfImmediateSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfImmediateSuccessor soFar summand@(LPESummand _ g _) = do
      inv <- isInvariant (cstrAnd (Set.fromList [guard, Subst.subst (Map.fromList paramEqs) Map.empty g]))
      return $ if inv then soFar ++ [summand] else soFar
    addSummandIfImmediateSuccessor soFar _ = do return soFar
-- getDefiniteSuccessors

