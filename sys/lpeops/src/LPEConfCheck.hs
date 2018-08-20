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
import qualified EnvData
import qualified Subst
import           TxsDefs hiding (guard)
import           LPEOps
import           Satisfiability
import           VarId
import           ValExpr
import           ConstDefs
import           VarFactory

chanIdConfluentIstep :: ChanId
chanIdConfluentIstep = ChanId (Text.pack "CISTEP") 969 []

getConfluentTauSummands :: LPESummands -> IOC.IOC LPESummands
getConfluentTauSummands summands = do
    confluentTauSummands <- Monad.filterM (isConfluentTauSummand summands) (filter isTauSummand summands)
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Detected " ++ (show (length confluentTauSummands)) ++ " confluent ISTEP summand(s)!") ]
    return confluentTauSummands
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
    else do let g1 = \e -> varSubst paramEqs1 (e :: TxsDefs.VExpr)
            let g2 = \e -> varSubst paramEqs2 (e :: TxsDefs.VExpr)
            -- Obtain all (fresh) variables used by the summand to communicate over a channel:
            let channelVars = Set.toList (foldl getChannelVars Set.empty channelOffers2)
            -- a1 == a1[g1] && ... && an == an[g1]
            g1_channelVars <- Monad.mapM g1 (map cstrVar channelVars)
            let channelArgEqs = map (\(channelVar, g1_channelVar) -> cstrEqual (cstrVar channelVar) g1_channelVar) (zip channelVars g1_channelVars)
            -- x1[g1][g2] == x1[g2][g1] && ... && xn[g1][g2] == xn[g2][g1]
            g1_params <- Monad.mapM g1 (map (cstrVar . fst) paramEqs2)
            g2_params <- Monad.mapM g2 (map (cstrVar . fst) paramEqs2)
            g2_g1_params <- Monad.mapM g2 g1_params
            g1_g2_params <- Monad.mapM g1 g2_params
            let instantiationEqs = map (\(x, y) -> cstrEqual x y) (zip g2_g1_params g1_g2_params)
            -- c1 && c2
            let premise = cstrAnd (Set.fromList [guard1, guard2])
            -- c1[g2] && c2[g1] && ...
            g2_guard1 <- g2 guard1
            g1_guard2 <- g1 guard2
            let conclusion = cstrAnd (Set.fromList ([g2_guard1, g1_guard2] ++ channelArgEqs ++ instantiationEqs))
            let confluenceCondition = cstrITE premise conclusion (cstrConst (Cbool True))
            inv <- isInvariant confluenceCondition
            return inv
  where
    getChannelVars :: Set.Set VarId -> LPEChannelOffer -> Set.Set VarId
    getChannelVars soFar (_chanId, commVars) = Set.union soFar (Set.fromList commVars)
-- checkConfluenceCondition

-- LPE rewrite method.
-- Appends confluent ISTEPs to predecessor summands.
confElm :: LPEOperation
confElm (channels, paramEqs, summands) = do
    confluentTauSummands <- getConfluentTauSummands summands
    if confluentTauSummands == []
    then do return $ Just (channels, paramEqs, summands)
    else do definiteSuccessors <- Monad.mapM (getDefiniteSuccessors summands) summands
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
      g' <- varSubst paramEqs g
      inv <- isInvariant (cstrAnd (Set.fromList [guard, g']))
      return $ if inv then soFar ++ [summand] else soFar
-- getDefiniteSuccessors

