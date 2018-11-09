{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
module TestUtils
(
createTestEnvC,
printInputExpectedFound,
validateLPEInstance,
tryLPEOperation
)
where

import Test.HUnit
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified EnvData
import Control.Monad.State
import TxsDefs
import qualified SMT
import Sigs

import TxsShow
import qualified Config
import qualified EnvCore as IOC
import qualified ParamCore
import qualified Solve.Params
import LPEPrettyPrint
import LPEOps
import ValExpr
import Constant

createTestEnvC :: IO IOC.EnvC
createTestEnvC = do
    smtEnv <- SMT.createSMTEnv (Maybe.fromJust (Config.getProc initConfig)) False -- Set to True to write SMT solver logs!
    (_info,smtEnv') <- runStateT SMT.openSolver smtEnv
    return $ IOC.EnvC { IOC.config = initConfig
                      , IOC.unid   = 0
                      , IOC.params = Config.updateParamVals initParams $ Config.configuredParameters initConfig
                      , IOC.state  = initState { IOC.smts = Map.singleton "current" smtEnv' }
                      }
  where
    initConfig = Config.defaultConfig
    initState = IOC.Initing { IOC.smts = Map.empty
                            , IOC.tdefs = TxsDefs.empty
                            , IOC.sigs = Sigs.empty
                            , IOC.putmsgs = putMsgs
                            , IOC.chanoffers = Map.empty
                            }
    initParams = Map.union ParamCore.initParams Solve.Params.initParams
-- createTestEnvC

putMsgs :: [EnvData.Msg] -> IOC.IOC ()
putMsgs msgs = do printMsg msgs
                  return ()
  where
    printMsg :: [EnvData.Msg] -> IOC.IOC ()
    printMsg [] = return ()
    printMsg (x:xs) = do liftIO $ putStrLn (pshow x)
                         printMsg xs
                         return ()
-- putMsgs

printInputExpectedFound :: LPEInstance -> LPEInstance -> LPEInstance -> String
printInputExpectedFound input expected found =
    "\nInput:\n\n" ++ showLPEInstance input ++
    "\n\nExpected output:\n\n" ++ showLPEInstance expected ++
    "\n\nActual output:\n\n" ++ showLPEInstance found ++ "\n"
-- printInputExpectedFound

validateLPEInstance' :: LPEInstance -> IOC.IOC (Maybe [String])
validateLPEInstance' lpeInstance = do
    (procInit, newProcId, newProcDef) <- fromLPEInstance lpeInstance "LPE" -- (This function is called within a new environment, so the name does not really matter.)
    tdefs <- gets (IOC.tdefs . IOC.state)
    let tdefs' = tdefs { TxsDefs.procDefs = Map.insert newProcId newProcDef (TxsDefs.procDefs tdefs) }
    IOC.modifyCS $ \st -> st { IOC.tdefs = tdefs' }
    eitherLpeInstance <- toLPEInstance procInit
    case eitherLpeInstance of
      Left msgs -> return (Just msgs)
      Right _ -> return Nothing
-- validateLPEInstance

validateLPEInstance :: LPEInstance -> IO (Maybe [String])
validateLPEInstance lpeInstance = do
    env <- createTestEnvC
    evalStateT (validateLPEInstance' lpeInstance) env
-- validateLPEInstance

tryLPEOperation :: LPEOperation -> LPEInstance -> LPEInstance -> IO ()
tryLPEOperation op input expected = do
    maybeV1 <- validateLPEInstance input
    case maybeV1 of
      Just msgs -> assertBool ("\nInvalid input LPE:\n\n" ++ showLPEInstance input ++ "\nProblems:\n\n" ++ List.intercalate "\n" msgs ++ "\n") False
      Nothing -> do maybeV2 <- validateLPEInstance expected
                    case maybeV2 of
                      Just msgs -> assertBool ("\nInvalid expected LPE:\n\n" ++ showLPEInstance expected ++ "\nProblems:\n\n" ++ List.intercalate "\n" msgs ++ "\n") False
                      Nothing -> do env <- createTestEnvC
                                    eitherFound <- evalStateT (op input "Out" (cstrConst (Cbool True))) env
                                    case eitherFound of
                                      Left msgs -> assertBool ("\nCould not produce output LPE:\n\n" ++ List.intercalate "\n" msgs ++ "\n") False
                                      Right found -> assertBool (printInputExpectedFound input expected found) (found==expected)
-- tryLPEOperation


