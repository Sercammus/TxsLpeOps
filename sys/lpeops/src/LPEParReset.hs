{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParReset
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParReset (
parReset
) where

import qualified Control.Monad       as Monad
import qualified Data.List           as List
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified FreeVar
import qualified EnvData
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           LPEPrettyPrint
import           VarId
import           ValExpr

-- LPE rewrite method.
-- Eliminates parameters that do not contribute to the behavior of a process from an LPE.
-- State spaces before and after are strongly bisimilar.
parReset :: LPEOperation
parReset lpeInstance@((_channels, paramEqs, summands)) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Identifying successors..." ]
    immediateSuccessors <- Monad.mapM (getImmediateSuccessors summands invariant) summands
    let successorsPerSummand = zipWith (\s i -> (s, i, map fst paramEqs)) summands immediateSuccessors
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Analyzing control flow..." ]
    newLPEInstance <- parResetLoop lpeInstance invariant successorsPerSummand
    return (Left newLPEInstance)
-- parReset

-- Selects all potential successors summands of a given summand from a list with all summands.
-- (In actuality, an overapproximation of all potential successors is selected, namely those
-- whose guard can be satisfied after the guard of the current summand has been satisfied and
-- after the substitutions of the process recursion have taken place.)
getImmediateSuccessors :: [LPESummand] -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getImmediateSuccessors _ _ (LPESummand _ _ LPEStop) = do return []
getImmediateSuccessors allSummands invariant (LPESummand _channelOffers guard (LPEProcInst paramEqs)) = do
    immediateSuccessors <- Monad.foldM addSummandIfImmediateSuccessor [] allSummands
    return $ immediateSuccessors
  where
    addSummandIfImmediateSuccessor :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    addSummandIfImmediateSuccessor soFar summand@(LPESummand _ g _) = do
      sat <- isSatisfiable (cstrAnd (Set.fromList [invariant, guard, varSubst paramEqs g]))
      return $ if sat then soFar ++ [summand] else soFar
-- getImmediateSuccessors

-- Updates the information collected about summands, in particular their lists of used variables,
-- until the information no longer changes.
-- With the final information, assign ANY values to variables that are unused:
parResetLoop :: LPEInstance -> TxsDefs.VExpr -> [(LPESummand, [LPESummand], [VarId])] -> IOC.IOC LPEInstance
parResetLoop lpeInstance@(channels, initParamEqs, summands) invariant successorsPerSummand = do
    let newSuccessorsPerSummand = parResetUpdate successorsPerSummand
    if newSuccessorsPerSummand == successorsPerSummand
    then do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Resetting the following parameters:" ]
            newSummands <- Monad.mapM (resetParamsInSummand lpeInstance invariant successorsPerSummand) summands
            return (channels, initParamEqs, newSummands)
    else parResetLoop lpeInstance invariant newSuccessorsPerSummand
-- parResetLoop

resetParamsInSummand :: LPEInstance -> TxsDefs.VExpr -> [(LPESummand, [LPESummand], [VarId])] -> LPESummand -> IOC.IOC LPESummand
resetParamsInSummand _ _ _ (summand@(LPESummand _ _ LPEStop)) = do return summand
resetParamsInSummand (_, initParamEqs, summands) invariant successorsPerSummand summand@(LPESummand channelOffers guard (LPEProcInst paramEqs)) =
    case [ (sucs, uvars) | (smd, sucs, uvars) <- successorsPerSummand, smd == summand ] of
      [(sucs, uvars)] -> if (length uvars) == (length initParamEqs)
                         then do return summand -- (All variables are used, apparently, so do not touch the summand.)
                         else do let nonSuccessors = Set.toList ((Set.fromList summands) Set.\\ (Set.fromList sucs))
                                 let newParamEqs = [ (p1, if p1 `elem` uvars then v2 else v1) | (p1, v1) <- initParamEqs, (p2, v2) <- paramEqs, p1 == p2 ]
                                 let smd2constraint = \(LPESummand _ g _) -> cstrAnd (Set.fromList [invariant, guard, varSubst newParamEqs g])
                                 notSat <- areNotSatisfiable (map smd2constraint nonSuccessors)
                                 if notSat
                                 then do printNewParamEqs newParamEqs
                                         return (LPESummand channelOffers guard (LPEProcInst newParamEqs))
                                 else  do return summand
      _ -> do return summand
  where
    printNewParamEqs :: LPEParamEqs -> IOC.IOC ()
    printNewParamEqs newParamEqs = do
        let changedParamEqs = [ ((p2, v2), (p1, v1)) | (p1, v1) <- newParamEqs, (p2, v2) <- paramEqs, p1 == p2, v1 /= v2 ]
        let Just summandNumber = (List.elemIndex summand summands)
        Monad.mapM_ (\((p, v), (_, w)) -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("\t" ++ (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr w) ++ " instead of " ++ (showValExpr v) ++ " in " ++ (numberToString (summandNumber + 1)) ++ " summand") ]) changedParamEqs
    
    numberToString :: Int -> String
    numberToString number =
        (show number) ++
        (case number `mod` 10 of
          1 -> "st"
          2 -> "nd"
          3 -> "rd"
          _ -> "th")
-- resetParamsInSummand

-- Updates the information collected about summands, in particular their lists of used variables:
parResetUpdate :: [(LPESummand, [LPESummand], [VarId])] -> [(LPESummand, [LPESummand], [VarId])]
parResetUpdate successorsPerSummand = map updateSummand successorsPerSummand
  where
    -- Initially, all variables are added to the list of used variables of a summand.
    -- They are removed only if:
    --  * They occur in the condition of the summand while not being defined as a communication variable, e.g. "CHANNEL ? x"; or
    --  * They are used in the assignment to a variable that IS used by a potential successor summand.
    updateSummand :: (LPESummand, [LPESummand], [VarId]) -> (LPESummand, [LPESummand], [VarId])
    updateSummand (summand, successors, _usedVars) =
        let relevantToSuccessorVars = foldl Set.union Set.empty (map getRelevantToSuccessorVars successors) in
          (summand, successors, Set.toList relevantToSuccessorVars)
    
    getRelevantToSuccessorVars :: LPESummand -> Set.Set VarId
    getRelevantToSuccessorVars successor@(LPESummand channelOffers guard procInst) =
        let usedVars = foldl (++) [] [uvars | (s, _g, uvars) <- successorsPerSummand, s == successor] in
        
        -- Parameters in the guard are relevant to the successor, because they enable/disable the channel+instantiation:
        let guardVars = Set.fromList (FreeVar.freeVars guard) in
        
        -- Parameters used in assignments to used variables are relevant (because the variables are used):
        let assignmentVars = (case procInst of
                                LPEProcInst paramEqs -> Set.fromList (foldl (++) [] [FreeVar.freeVars v | (p, v) <- paramEqs, q <- usedVars, p == q])
                                _ -> Set.empty) in
        
        -- The successor communicates via these variables, so their values are NOT relevant to the successor:
        let channelOfferVars = Set.fromList (foldl (++) [] (map snd channelOffers)) in
        
        -- Combine them all:
          (Set.union guardVars assignmentVars) Set.\\ channelOfferVars
-- parResetUpdate

