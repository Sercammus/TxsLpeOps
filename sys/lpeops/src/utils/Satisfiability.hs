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
showSolution
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
import ConstDefs hiding (sort)
import ValExprVisitor
import ValExprPrettyPrint
import VarFactory
import VarId
import ValExpr

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
                          else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
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
                     _ -> if True -- Solve.isEasySolve frees assertions
                          then do (sol, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putSMT "current" smtEnv'
                                  case sol of
                                    SolveDefs.Solved solMap -> return (Just (Map.map cstrConst solMap))
                                    _ -> return Nothing
                          else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> ?") ]
                                  (sol, _smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: " ++ (showValExpr expr) ++ " ==> " ++ (showSolution sol)) ]
                                  -- IOC.putSMT "current" smtEnv'
                                  IOC.putMsgs [ EnvData.TXS_CORE_ANY ("SMT log: Lazy 2") ]
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
anyElm expr = visitValExprM anyElmVisitorM expr
  where
    anyElmVisitorM :: TxsDefs.VExpr -> IOC.IOC (Maybe TxsDefs.VExpr)
    anyElmVisitorM (view -> Vconst (Cany sort)) = do varId <- createFreshVar sort
                                                     return $ Just (cstrVar varId)
    anyElmVisitorM _                            = do return $ Nothing
-- anyElm

