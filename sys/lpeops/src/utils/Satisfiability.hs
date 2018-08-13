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
getSomeSolution
) where

import Control.Monad.State
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified FreeVar
import qualified Solve
import qualified SolveDefs
import qualified SortId
import qualified SortOf
import qualified SMTData
import ConstDefs hiding (sort)
import VarId
import ValExpr
import ValExprVisitor
import VarFactory

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
                     _ -> do (sat, smtEnv') <- lift $ runStateT (Solve.satSolve frees assertions) smtEnv
                             IOC.putSMT "current" smtEnv'
                             IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Expression: " ++ (show expr)) ]
                             return sat
-- getSat

-- Frequently used method; code is modified code from TxsCore.
-- Attempts to find a solution for the given expression.
getSomeSolution :: TxsDefs.VExpr -> IOC.IOC SolveDefs.SolveProblem
getSomeSolution expression = do
    envc <- get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'solve' without model" ]
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
                     _ -> do (solution, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
                             IOC.putSMT "current" smtEnv'
                             IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Expression: " ++ (show expr)) ]
                             return solution
-- getSomeSolution

-- Eliminates occurrences of ANY by substituting them for fresh, free variables.
anyElm :: ValExpr VarId -> IOC.IOC (ValExpr VarId)
anyElm expr = visitValExpr anyElmVisitor expr

-- Visitor for anyElm:
anyElmVisitor :: ValExpr VarId -> IOC.IOC (ValExpr VarId)
anyElmVisitor (view -> Vconst (Cany sort)) = do varId <- createFreshVar sort
                                                return $ cstrVar varId
anyElmVisitor expr                         = do return $ expr

