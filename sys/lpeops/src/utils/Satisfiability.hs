{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Satisfiability
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module Satisfiability (
isInvariant,
isSatisfiable,
isUnsatisfiable,
getSomeSolution,
showSolution,
createVarSubst,
varSubst
) where

import Control.Monad.State
import qualified EnvCore as IOC
import qualified EnvData
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified FreeVar
import qualified Solve
import qualified SolveDefs
import qualified SortId
import qualified SortOf
import qualified SMTData
import Constant hiding (sort)
import ValExprVisitor
import ValExprPrettyPrint
import VarFactory
import VarId
import ValExpr
import CstrId

-- Checks if the specified expression cannot be false.
isInvariant :: TxsDefs.VExpr -> IOC.IOC Bool
isInvariant expression = isUnsatisfiable (cstrNot expression)

-- Checks if the specified expression can be true.
isSatisfiable :: TxsDefs.VExpr -> IOC.IOC Bool
isSatisfiable expression = do sat <- getSat expression
                              case sat of
                                SolveDefs.Sat -> return True
                                _ -> return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isUnsatisfiable :: TxsDefs.VExpr -> IOC.IOC Bool
isUnsatisfiable expression = do sat <- getSat expression
                                case sat of
                                  SolveDefs.Unsat -> return True
                                  _ -> return False
-- isUnsatisfiable

-- Frequently used method; code is modified code from TxsCore.
-- Checks whether the given expression is satisfiable.
getSat :: TxsDefs.VExpr -> IOC.IOC SolveDefs.SolvableProblem
getSat expression = do
    envc <- get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'satsolve' without model" ]
                       return SolveDefs.Unknown
      _ -> if SortOf.sortOf expression /= SortId.sortIdBool
           then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "Value expression shall be Bool" ]
                   return SolveDefs.Unknown
           else do expr <- anyElm expression
                   let frees = FreeVar.freeVars expr
                   let assertions = Solve.add expr Solve.empty
                   smtEnv <- IOC.getSMT "current"
                   case smtEnv of
                     SMTData.SmtEnvError -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Could not locate SMT solver" ]
                                               return SolveDefs.Unknown
                     _ -> if Solve.isEasySolve frees assertions
                          then do (sat, smtEnv') <- lift $ runStateT (Solve.satSolve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  return sat
                          else do --IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
                                  (sat, smtEnv') <- lift $ runStateT (Solve.satSolve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> " ++ (show sat)) ]
                                  IOC.putSMT "current" smtEnv'
                                  return sat
-- getSat

-- Frequently used method; code is modified code from TxsCore.
-- Attempts to find a solution for the given expression.
getSomeSolution :: TxsDefs.VExpr -> [VarId] -> IOC.IOC (Maybe (Map.Map VarId TxsDefs.VExpr))
getSomeSolution expression variables = do
    envc <- get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'solve' without model" ]
                       return Nothing
      _ -> if SortOf.sortOf expression /= SortId.sortIdBool
           then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "Value expression shall be Bool" ]
                   return Nothing
           else do expr <- anyElm expression
                   let frees = Set.toList (Set.fromList ((FreeVar.freeVars expr) ++ variables))
                   let assertions = Solve.add expr Solve.empty
                   smtEnv <- IOC.getSMT "current"
                   case smtEnv of
                     SMTData.SmtEnvError -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY "Could not locate SMT solver" ]
                                               return Nothing
                     _ -> if Solve.isEasySolve frees assertions
                          then do (sol, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (Map.map cstrConst solMap))
                                    _ -> return Nothing
                          else do --IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
                                  (sol, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> " ++ (showSolution sol)) ]
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (Map.map cstrConst solMap))
                                    _ -> return Nothing
-- getSomeSolution

showSolution :: SolveDefs.SolveProblem VarId -> String
showSolution SolveDefs.Unsolvable = "Unsolvable"
showSolution SolveDefs.UnableToSolve = "UnableToSolve"
showSolution (SolveDefs.Solved solMap) =
    let f = \(p, v) -> (Text.unpack (VarId.name p)) ++ " := " ++ (showValExpr (cstrConst v)) in
      "Solved [" ++ (separatedList (map f (Map.toList solMap)) ", ") ++ "]"
  where
    separatedList :: [String] -> String -> String
    separatedList [] _ = ""
    separatedList [x] _ = x
    separatedList (x1:x2:xs) separator = x1 ++ separator ++ (separatedList (x2:xs) separator)
-- showSolution

-- Eliminates occurrences of ANY by substituting them for fresh, free variables.
anyElm :: TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
anyElm expr = visitValExpr anyElmVisitorM expr
  where
    anyElmVisitorM :: [IOC.IOC TxsDefs.VExpr] -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
    anyElmVisitorM _ (view -> Vconst (Cany sort)) = do varId <- createFreshVar sort
                                                       return (cstrVar varId)
    anyElmVisitorM vexps parentExpr = defaultValExprVisitorM vexps parentExpr
-- anyElm

createVarSubst :: [(VarId, TxsDefs.VExpr)] -> (TxsDefs.VExpr -> TxsDefs.VExpr)
createVarSubst substEqs = (\e -> varSubst substEqs (e :: TxsDefs.VExpr))

-- Substitutes variables in a boolean expression while avoiding invalid subexpressions.
-- This is useful when substituting into expressions that will be SAT-checked:
varSubst :: [(VarId, TxsDefs.VExpr)] -> TxsDefs.VExpr -> TxsDefs.VExpr
varSubst substEqs expr =
    let (valid, result) = visitValExpr validityVisitor expr in
      if valid
      then result
      else cstrConst (Cbool False)
  where
    -- The first element of the pair is the condition under which the second element is a DEFINED value.
    -- We abbreviate this with dc, for 'defined condition'.
    validityVisitor :: [(Bool, TxsDefs.VExpr)] -> TxsDefs.VExpr -> (Bool, TxsDefs.VExpr)
    validityVisitor _ (view -> Vvar varId) =
         -- Perform the substitution:
        case [v | (p, v) <- substEqs, p == varId] of
          [v] -> (True, v)
          _ -> (True, cstrVar varId)
    validityVisitor [(valid, cstrExpr@(view -> Vconst (Ccstr c2 _fields)))] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if c1 == c2
        then (valid, cstrAccess c1 p cstrExpr)
        else (False, cstrConst (Cany (CstrId.cstrsort c1)))
    validityVisitor [(valid, cstrExpr@(view -> Vcstr c2 _fields))] (view -> Vaccess c1 p _vexp) =
        -- If a non-existent field is accessed, the value becomes undefined + unsatisfiable:
        if (c1 == c2)
        then (valid, cstrAccess c1 p cstrExpr)
        else (False, cstrConst (Cany (CstrId.cstrsort c1)))
    validityVisitor vexps parentExpr =
        -- Usually, the parent expression is unsatisfiable if the children are unsatisfiable:
        (combineValidity vexps, defaultValExprVisitor (map snd vexps) parentExpr)
    -- validityVisitor
    
    combineValidity :: [(Bool, TxsDefs.VExpr)] -> Bool
    combineValidity [] = True
    combineValidity [(valid, _)] = valid
    combineValidity ((valid, _):xs) = valid && (combineValidity xs)
-- varSubst


