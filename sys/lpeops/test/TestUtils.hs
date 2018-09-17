{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
module TestUtils
(
createTestEnvC,
printInputExpectedFound
)
where
 
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
import LPETypes

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
    printMsg [] = do return ()
    printMsg (x:xs) = do liftIO $ putStrLn (pshow x)
                         printMsg xs
                         return ()
-- putMsgs

printInputExpectedFound :: LPEInstance -> LPEInstance -> LPEInstance -> String
printInputExpectedFound input expected found =
    --"\n" ++ (splitPrint "   Input..." (show input) 120) ++ "\n-->\n\n" ++ (printSideBySide "Expected..." "   Found..." (show expected) (show found) 120)
    "\nInput:\n\n" ++ (showLPEInstance input) ++
    "\n\nExpected output:\n\n" ++ (showLPEInstance expected) ++
    "\n\nActual output:\n\n" ++ (showLPEInstance found) ++ "\n"
-- printInputExpectedFound

