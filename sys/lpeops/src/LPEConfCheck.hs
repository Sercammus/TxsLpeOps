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

import qualified Data.List           as List
import qualified Data.Map            as Map
import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified VarId
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
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<confCheck>>" ]
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
    else do -- a1 == a1[g1] && ... && an == an[g1]
            channelArgEqs <- Monad.mapM getChannelArgEq channelVars2
            
            -- x1[g1][g2] == x1[g2][g1] && ... && xn[g1][g2] == xn[g2][g1]
            instantiationEqs <- Monad.mapM getInstantiationEq (Map.keys paramEqs2)
            
            -- c1 && c2
            let premise = cstrAnd (Set.fromList [guard1, guard2])
            
            -- c1[g2] && c2[g1] && ...
            g1 <- doBlindSubst paramEqs2 guard1
            g2 <- doBlindSubst paramEqs1 guard2
            let conclusion = cstrAnd (Set.fromList ([g1, g2] ++ channelArgEqs ++ instantiationEqs))
            
            -- Combine them all:
            let confluenceCondition = cstrITE premise conclusion (cstrConst (Cbool True))
            
            -- Is the confluence condition a tautology?
            taut <- isTautology confluenceCondition invariant
            return taut
  where
    getChannelArgEq :: VarId.VarId -> IOC.IOC TxsDefs.VExpr
    getChannelArgEq param = do
        let paramExpr = cstrVar param
        e' <- doBlindSubst paramEqs1 paramExpr
        return (cstrEqual paramExpr e')
    -- getChannelArgEq
    
    getInstantiationEq :: VarId.VarId -> IOC.IOC TxsDefs.VExpr
    getInstantiationEq param = do
        let paramExpr = cstrVar param
        e1 <- doBlindSubst paramEqs2 paramExpr
        e1' <- doBlindSubst paramEqs1 e1
        e2 <- doBlindSubst paramEqs1 paramExpr
        e2' <- doBlindSubst paramEqs2 e2
        return (cstrEqual e1' e2')
    -- getInstantiationEq
-- checkConfluenceCondition

-- LPE rewrite method.
-- Appends confluent ISTEPs to predecessor summands.
confElm :: LPEOperation
confElm (channels, paramEqs, summands) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<confElm>>" ]
    confluentTauSummands <- getConfluentTauSummands summands invariant
    if confluentTauSummands == []
    then do return $ Right (channels, paramEqs, summands)
    else do definiteSuccessors <- Monad.mapM (getDefiniteSuccessors summands invariant) summands
            let confluentTauSuccessors = map (List.intersect confluentTauSummands) definiteSuccessors
            mergedSummands <- Monad.mapM mergeZippedSummands (zip summands confluentTauSuccessors)
            return $ Right (channels, paramEqs, mergedSummands)
  where
    mergeZippedSummands :: (LPESummand, [LPESummand]) -> IOC.IOC LPESummand
    mergeZippedSummands (summand, []) = do return summand
    mergeZippedSummands (summand@(LPESummand _ _ _ LPEStop), _) = do return summand
    mergeZippedSummands (summand@(LPESummand chanVars chanOffers g1 (LPEProcInst eqs1)), (confluentTauSuccessor:_)) = do
        case confluentTauSuccessor of
          LPESummand _ _ _ (LPEProcInst eqs2) -> do newEqs <- doBlindParamEqsSubst eqs1 eqs2
                                                    return (LPESummand chanVars chanOffers g1 (LPEProcInst newEqs))
          LPESummand _ _ _ LPEStop -> return summand
-- confElm













