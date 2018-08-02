{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEOps
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEOps (
LPEOperation,
lpeOperation,
dummyOp,
smtTest,
module LPETypes
) where

import qualified EnvCore as IOC
import qualified TxsDefs
import           LPETypes
import           Name

import Control.Monad.State
import qualified Data.Text as Text
import qualified Data.Set as Set
import qualified Data.Map as Map
import StdTDefs (stdSortTable)
import qualified EnvData
import ValExpr
import qualified VarId
import qualified SortId
import ConstDefs
import Data.Maybe
-- import qualified FreeVar
import qualified Solve
import qualified SolveDefs
import Subst
import qualified FreeMonoidX as FMX

type LPEOperation = LPEInstance -> IOC.IOC (Maybe LPEInstance)

-- Core method that does the following:
--  1. Transforms a closed process expression to an LPE instance;
--  2. Applies the given operation to the LPE instance, which results in a new LPE instance;
--  3. Transforms the new LPE instance to a process definition with the specified name and
--     a process expression that creates an instance of this process definition.
lpeOperation :: LPEOperation -> TxsDefs.BExpr -> Name -> IOC.IOC (Maybe (TxsDefs.BExpr, TxsDefs.ProcDef))
lpeOperation operation procInst name = do
    maybeLPEInstance <- toLPEInstance procInst
    case maybeLPEInstance of
      Just lpeInstance -> do maybeNewLPEInstance <- operation lpeInstance
                             case maybeNewLPEInstance of
                               Just newLPEInstance -> do temp <- fromLPEInstance newLPEInstance name
                                                         return (Just temp)
                               _ -> do return Nothing
      _ -> do return Nothing
-- lpeOperation

dummyOp :: LPEOperation
dummyOp lpeInstance = do return (Just lpeInstance)

intSort :: SortId.SortId
intSort = fromMaybe (error "LPEOps: could not find standard IntSort") (Map.lookup (Text.pack "Int") stdSortTable)

createIntVar :: String -> IOC.IOC VarId.VarId
createIntVar name = do
    varXUnid <- IOC.newUnid
    return VarId.VarId { VarId.name = Text.pack name, VarId.unid = varXUnid, VarId.varsort = intSort }

smtTest :: LPEOperation
smtTest lpeInstance = do
    envc <- get
    case IOC.state envc of
      IOC.Noning -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR "No 'solve' without model" ]
                       return Nothing
      _ -> do varX <- createIntVar "x$x"
              varY <- createIntVar "x$y"
              varZ <- createIntVar "x$any"
              let expr1 = cstrEqual (cstrVar varX) (cstrConst (Cint 12))
              let expr2 = cstrEqual (cstrVar varX) (cstrVar varY)
              let expr3 = cstrEqual (cstrVar varY) (cstrSum (FMX.fromListT [cstrVar varX, cstrConst (Cany intSort)]))
              let expr4 = cstrEqual (cstrVar varZ) (cstrConst (Cany intSort))
              let expr = cstrAnd (Set.fromList [expr1, expr2, expr3, expr4])
              IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Expression = " ++ (show expr)) ]
              let frees = [varX, varY, varZ]
              let renamedFrees = [(frees !! i) { VarId.name = Text.pack ("fv" ++ (show i)) } | i <- [0..(length frees) - 1]]
              let rho = \e -> Subst.subst (Map.fromList (zip frees (map cstrVar renamedFrees))) Map.empty (e :: TxsDefs.VExpr)
              let assertions = Solve.add (rho expr) Solve.empty
              smtEnv <- IOC.getSMT "current"
              -- IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Frees? " ++ (show frees)) ]
              (sat, smtEnv') <- lift $ runStateT (Solve.solve frees assertions) smtEnv
              IOC.putSMT "current" smtEnv' -- It is okay that obtained results are reused later?
              case sat of
                SolveDefs.Solved _ -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Satisfiable? Yes!") ]
                _ -> do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Satisfiable? Not necessarily!") ]
              return (Just lpeInstance)



