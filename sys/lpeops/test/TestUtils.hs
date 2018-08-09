{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
module TestUtils
(
createTestEnvC,
splitString,
splitPrint,
printSideBySide,
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

import qualified Config
import qualified EnvCore as IOC
import qualified ParamCore
import qualified Solve.Params
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
    printMsg (x:xs) = do liftIO $ putStrLn (show x)
                         printMsg xs
                         return ()
-- putMsgs

splitString :: String -> Int -> [String]
splitString [] _ = []
splitString str segmentLength =
    let firstSegment = map snd (zip [0..(segmentLength-1)] str) in
    let remainingSegments = map snd (filter (\x -> (fst x) >= segmentLength) (zip [0..(length str)] str)) in
      firstSegment:(splitString remainingSegments segmentLength)
-- splitString

makeLength :: [String] -> Int -> [String]
makeLength segments targetLength =
    if (length segments) >= targetLength then segments else makeLength (segments ++ [[]]) targetLength
-- makeLength

splitPrint :: String -> String -> Int -> String
splitPrint header str lineLength =
    let segments = splitString str lineLength in
      foldl (\soFar seg -> soFar ++ header ++ seg ++ "\n") "" segments
-- splitPrint

printSideBySide :: String -> String -> String -> String -> Int -> String
printSideBySide header1 header2 s1 s2 lineLength =
    let segs1 = splitString s1 lineLength in
    let segments2 = makeLength (splitString s2 lineLength) (length segs1) in
    let segments1 = makeLength segs1 (length segments2) in
      foldl (\soFar (seg1, seg2) -> soFar ++ header1 ++ seg1 ++ "\n" ++ header2 ++ seg2 ++ "\n\n") "" (zip segments1 segments2)
-- printSideBySide

printInputExpectedFound :: LPEInstance -> LPEInstance -> LPEInstance -> String
printInputExpectedFound input expected found =
    "\n" ++ (splitPrint "   Input..." (show input) 120) ++ "\n-->\n\n" ++ (printSideBySide "Expected..." "   Found..." (show expected) (show found) 120)
-- printInputExpectedFound

