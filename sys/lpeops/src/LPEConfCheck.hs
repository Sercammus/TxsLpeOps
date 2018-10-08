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
import           ValExpr
import           Constant
import           LPESuccessors

chanIdConfluentIstep :: ChanId
chanIdConfluentIstep = ChanId (Text.pack "CISTEP") 969 []

getConfluentTauSummands :: LPESummands -> TxsDefs.VExpr -> IOC.IOC LPESummands
getConfluentTauSummands summands invariant = do
    confluentTauSummands <- Monad.filterM (isConfluentTauSummand summands invariant) (filter isTauSummand summands)
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Detected " ++ (show (length confluentTauSummands)) ++ " confluent ISTEP summand(s)!") ]
    return confluentTauSummands
-- getConfluentTauSummands

-- LPE rewrite method.
-- Flags confluent ISTEPs by renaming them to CISTEPs.
confCheck :: LPEOperation
confCheck (channels, paramEqs, summands) _out invariant = do
    confluentTauSummands <- getConfluentTauSummands summands invariant
    let noConfluentTauSummands = (Set.fromList summands) Set.\\ (Set.fromList confluentTauSummands)
    let newSummands = Set.union noConfluentTauSummands (Set.fromList (map flagTauSummand confluentTauSummands))
    do return (Right (channels, paramEqs, Set.toList newSummands))
-- confCheck

isTauSummand :: LPESummand -> Bool
isTauSummand (LPESummand _ [(chanId, _)] _ _) = chanId == chanIdIstep
isTauSummand _ = False
-- isTauSummand

flagTauSummand :: LPESummand -> LPESummand
flagTauSummand (LPESummand chanVars [(_chanId, commVars)] guard paramEqs) = (LPESummand chanVars [(chanIdConfluentIstep, commVars)] guard paramEqs)
flagTauSummand tauSummand = tauSummand

isConfluentTauSummand :: [LPESummand] -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
isConfluentTauSummand [] _ _ = do return True
isConfluentTauSummand (x:xs) invariant tauSummand = do
    check <- checkConfluenceCondition tauSummand x invariant
    if check
    then isConfluentTauSummand xs invariant tauSummand
    else do return False
-- isConfluentTauSummand

checkConfluenceCondition :: LPESummand -> LPESummand -> TxsDefs.VExpr -> IOC.IOC Bool
checkConfluenceCondition (LPESummand _ _ _ LPEStop) _ _ = do return False
checkConfluenceCondition _ (LPESummand _ _ _ LPEStop) _ = do return False
checkConfluenceCondition (summand1@(LPESummand _channelVars1 _channelOffers1 guard1 (LPEProcInst paramEqs1))) (summand2@(LPESummand channelVars2 _channelOffers2 guard2 (LPEProcInst paramEqs2))) invariant = do
    if summand1 == summand2
    then do return True
    else do -- Create functions that can do the required substitutions in a convenient manner.
            -- For the entire condition, these functions should only be computed once!
            let g1 = createVarSubst paramEqs1
            let g2 = createVarSubst paramEqs2
            
            -- a1 == a1[g1] && ... && an == an[g1]
            let channelArgEqs = map (\channelVar -> cstrEqual channelVar (g1 channelVar)) (map cstrVar channelVars2)
            
            -- x1[g1][g2] == x1[g2][g1] && ... && xn[g1][g2] == xn[g2][g1]
            let instantiationEqs = map (\p -> cstrEqual (g1 (g2 p)) (g2 (g1 p))) (map (cstrVar . fst) paramEqs2)
            
            -- c1 && c2
            let premise = cstrAnd (Set.fromList [guard1, guard2])
            -- c1[g2] && c2[g1] && ...
            let conclusion = cstrAnd (Set.fromList ([g2 guard1, g1 guard2] ++ channelArgEqs ++ instantiationEqs))
            
            -- Combine them all:
            let confluenceCondition = cstrITE premise conclusion (cstrConst (Cbool True))
            
            -- Is the confluence condition a tautology?
            taut <- isTautology (cstrAnd (Set.fromList [invariant, confluenceCondition]))
            return taut
-- checkConfluenceCondition

-- LPE rewrite method.
-- Appends confluent ISTEPs to predecessor summands.
confElm :: LPEOperation
confElm (channels, paramEqs, summands) _out invariant = do
    confluentTauSummands <- getConfluentTauSummands summands invariant
    if confluentTauSummands == []
    then do return $ Right (channels, paramEqs, summands)
    else do definiteSuccessors <- Monad.mapM (getDefiniteSuccessors summands invariant) summands
            let confluentTauSuccessors = map (List.intersect confluentTauSummands) definiteSuccessors
            return $ Right (channels, paramEqs, zipWith mergeSummands summands confluentTauSuccessors)
  where
    mergeSummands :: LPESummand -> [LPESummand] -> LPESummand
    mergeSummands summand [] = summand
    mergeSummands summand@(LPESummand _ _ _ LPEStop) _ = summand
    mergeSummands summand@(LPESummand chanVars chanOffers g1 (LPEProcInst eqs1)) (confluentTauSuccessor:_) =
        case confluentTauSuccessor of
          LPESummand _ _ _ (LPEProcInst eqs2) ->
            let substitution = \e -> Subst.subst (Map.fromList eqs1) Map.empty (e :: TxsDefs.VExpr) in
              LPESummand chanVars chanOffers g1 (LPEProcInst [ (p, substitution v) | (p, v) <- eqs2 ])
          LPESummand _ _ _ LPEStop -> summand
-- confElm

