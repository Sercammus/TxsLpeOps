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
import qualified Data.List           as List
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

getConfluentTauSummands :: LPESummands -> IOC.IOC LPESummands
getConfluentTauSummands summands = do
    Monad.filterM (isConfluentTauSummand summands) (filter isTauSummand summands)
-- getConfluentTauSummands

-- LPE rewrite method.
-- Flags confluent ISTEPs by renaming them to CISTEPs.
confCheck :: LPEOperation
confCheck (channels, paramEqs, summands) = do
    confluentTauSummands <- getConfluentTauSummands summands
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

-- isFlaggedTauSummand :: LPESummand -> Bool
-- isFlaggedTauSummand (LPESummand [(chanId, _)] _ _) = chanId == chanIdConfluentIstep
-- isFlaggedTauSummand _ = False
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
checkConfluenceCondition (LPESummand _ _ LPEStop) _ = do return False
checkConfluenceCondition _ (LPESummand _ _ LPEStop) = do return False
checkConfluenceCondition (summand1@(LPESummand _channelOffers1 guard1 (LPEProcInst paramEqs1))) (summand2@(LPESummand channelOffers2 guard2 (LPEProcInst paramEqs2))) = do
    if summand1 == summand2
    then do return True
    else do let channelVars = Set.toList (foldl getChannelVars Set.empty channelOffers2)
            -- a1 == a1[g1] && ... && an == an[g1]
            let channelArgEqs = map (\varId -> cstrEqual (cstrVar varId) (g1 (cstrVar varId))) channelVars
            -- x1[g1][g2] == x1[g2][g1] && ... && xn[g1][g2] == xn[g2][g1]
            let instantiationEqs = map (\(p, _) -> cstrEqual (g1 (g2 (cstrVar p))) (g2 (g1 (cstrVar p)))) paramEqs2
            -- c1 && c2
            let premise = cstrAnd (Set.fromList [guard1, guard2])
            -- c1[g2] && c2[g1] && ...
            let conclusion = cstrAnd (Set.fromList ([g2 guard1, g1 guard2] ++ channelArgEqs ++ instantiationEqs))
            let confluenceCondition = cstrITE premise conclusion (cstrConst (Cbool { cBool=True }))
            inv <- isInvariant confluenceCondition
            return inv
  where
    getChannelVars :: Set.Set VarId -> LPEChannelOffer -> Set.Set VarId
    getChannelVars soFar (_chanId, commVars) = Set.union soFar (Set.fromList commVars)
    
    g1 = \e -> Subst.subst (Map.fromList paramEqs1) Map.empty (e :: TxsDefs.VExpr)
    g2 = \e -> Subst.subst (Map.fromList paramEqs2) Map.empty (e :: TxsDefs.VExpr)
-- checkConfluenceCondition

-- LPE rewrite method.
-- Appends confluent ISTEPs to predecessor summands.
confElm :: LPEOperation
confElm (channels, paramEqs, summands) = do
    confluentTauSummands <- getConfluentTauSummands summands
    definiteSuccessors <- Monad.mapM (getDefiniteSuccessors summands) summands
    let confluentTauSuccessors = map (List.intersect confluentTauSummands) definiteSuccessors
    return $ Just (channels, paramEqs, zipWith mergeSummands summands confluentTauSuccessors)
  where
    mergeSummands :: LPESummand -> [LPESummand] -> LPESummand
    mergeSummands summand [] = summand
    mergeSummands summand@(LPESummand _ _ LPEStop) _ = summand
    mergeSummands summand@(LPESummand chans g1 (LPEProcInst eqs1)) (confluentTauSuccessor:_) =
        case confluentTauSuccessor of
          LPESummand _ _ (LPEProcInst eqs2) ->
            let substitution = \e -> Subst.subst (Map.fromList eqs1) Map.empty (e :: TxsDefs.VExpr) in
              LPESummand chans g1 (LPEProcInst [ (p, substitution v) | (p, v) <- eqs2 ])
          LPESummand _ _ LPEStop -> summand
-- confElm

-- Selects all summands from a given list that are definitely successors of a given summand.
-- The result is an underapproximation!
getDefiniteSuccessors :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
getDefiniteSuccessors _ (LPESummand _ _ LPEStop) = do return []
getDefiniteSuccessors allSummands (LPESummand _channelOffers guard (LPEProcInst paramEqs)) = do
    immediateSuccessors <- Monad.foldM addSummandIfDefiniteSuccessor [] allSummands
    return $ immediateSuccessors
  where
    addSummandIfDefiniteSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfDefiniteSuccessor soFar summand@(LPESummand _ g _) = do
      inv <- isInvariant (cstrAnd (Set.fromList [guard, Subst.subst (Map.fromList paramEqs) Map.empty g]))
      return $ if inv then soFar ++ [summand] else soFar
-- getDefiniteSuccessors
