{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
     
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module TestConstElm
(
testConstElm
)
where
 
import Test.HUnit
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import qualified EnvData
import Control.Monad.State
import TxsDefs
import ProcId
import ChanId
import SortId
import qualified Data.Text         as T
import qualified SMT
import VarId
import ConstDefs
import ValExpr
import Sigs

import qualified Config
import qualified EnvCore as IOC
import qualified ParamCore
import qualified Solve.Params
import StdTDefs (stdSortTable)

import LPEOps
import LPEConstElm

initializeEnvC :: IO IOC.EnvC
initializeEnvC = do
    smtEnv <- SMT.createSMTEnv (Maybe.fromJust (Config.getProc initConfig)) True
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
-- initializeEnvC

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

constElmFunc :: LPEInstance -> IO (Maybe LPEInstance)
constElmFunc lpeInstance = do
    env <- initializeEnvC
    evalStateT (constElm lpeInstance) env
-- constElmFunc

testConstElm :: Test
testConstElm = TestCase $ do
    maybeResult <- constElmFunc lpeInstance1
    case maybeResult of
      Just result -> assertBool ("\n" ++ (splitPrint "   Input..." (show lpeInstance1) 120) ++ "\n-->\n\n" ++ (printSideBySide "Expected..." "   Found..." (show lpeInstance2) (show result) 120)) (result==lpeInstance2)
      _ -> assertBool "Function constElm failed to produce output!" False
  where
    summand1_1 :: LPESummand
    summand1_1 = LPESummand -- A ? z [z==0] >-> P(1, 0)
        [(chanIdA, [varIdZ])]
        (cstrEqual vexprZ vexpr0)
        [(varIdX, vexpr1), (varIdY, vexpr0)]
    summand1_2 :: LPESummand
    summand1_2 = LPESummand -- A ? y [x==1 && y==0] >-> P(0, y)
        [(chanIdA, [varIdY])]
        (cstrAnd (Set.fromList [cstrEqual vexprX vexpr1, cstrEqual vexprY vexpr0]))
        [(varIdX, vexpr0), (varIdY, vexprY)]
    lpeInstance1 :: LPEInstance
    lpeInstance1 = ([chanIdA], [(varIdX, vexpr0), (varIdY, vexpr0)], [summand1_1, summand1_2])
    
    summand2_1 :: LPESummand
    summand2_1 = LPESummand -- A ? z [z==0] >-> P(1)
        [(chanIdA, [varIdZ])]
        (cstrEqual vexprZ vexpr0)
        [(varIdX, vexpr1)]
    summand2_2 :: LPESummand
    summand2_2 = LPESummand -- A ? __FV1 [0==0 && x==1] >-> P(0)
        [(chanIdA, [varIdFV1])]
        (cstrAnd (Set.fromList [cstrEqual vexprX vexpr1, cstrEqual vexpr0 vexpr0]))
        [(varIdX, vexpr0)]
    lpeInstance2 :: LPEInstance
    lpeInstance2 = ([chanIdA], [(varIdX, vexpr0)], [summand2_1, summand2_2])
-- testConstElm

---------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------

procIdGen :: String -> [ChanId] -> [VarId] -> ProcId
procIdGen name' chans vars' = ProcId   {  ProcId.name       = T.pack name'
                                        , ProcId.unid       = 111
                                        , ProcId.procchans  = chans
                                        , ProcId.procvars   = vars'
                                        , ProcId.procexit   = NoExit
                                    }

varIdX :: VarId
varIdX = VarId (T.pack "x") 33 intSort
varIdY :: VarId
varIdY = VarId (T.pack "y") 36 intSort
varIdZ :: VarId
varIdZ = VarId (T.pack "z") 36 intSort
varIdA1 :: VarId
varIdA1 = VarId (T.pack "A$1") 34 intSort
varIdB1 :: VarId
varIdB1 = VarId (T.pack "B$1") 34 intSort
varIdFV1 :: VarId
varIdFV1 = VarId (T.pack "__FV1") (-1) intSort

vexprX :: VExpr
vexprX = cstrVar varIdX
vexprY :: VExpr
vexprY = cstrVar varIdY
vexprZ :: VExpr
vexprZ = cstrVar varIdZ
vexprA1 :: VExpr
vexprA1 = cstrVar varIdA1
vexprB1 :: VExpr
vexprB1 = cstrVar varIdB1
vexprFV1 :: VExpr
vexprFV1 = cstrVar varIdFV1

vexpr0 :: VExpr
vexpr0 = cstrConst (Cint 0)
vexpr1 :: VExpr
vexpr1 = cstrConst (Cint 1)
vexpr2 :: VExpr
vexpr2 = cstrConst (Cint 2)
vexprMin1 :: VExpr
vexprMin1 = cstrConst (Cint (-1))

int0 :: VExpr               -- PvdL : what is the difference with vexpr0?
int0 = cstrConst (Cint 0)
int1 :: VExpr
int1 = cstrConst (Cint 1)
int2 :: VExpr
int2 = cstrConst (Cint 2)
varIdPcP :: VarId
varIdPcP = VarId (T.pack "pc$P") 0 intSort
vexprPcP :: VExpr
vexprPcP = cstrVar varIdPcP


-- action: A!1
actOfferA1 :: ActOffer
actOfferA1   = ActOffer {  offers = Set.singleton
                                        Offer { chanid = chanIdA
                                              , chanoffers = [Exclam vexpr1]
                                        }
                        , hiddenvars = Set.empty
                        , constraint = cstrConst (Cbool True)
            }

-- action: A?x
actOfferAx :: ActOffer
actOfferAx   = ActOffer {  offers = Set.singleton
                                        Offer { chanid = chanIdA
                                              , chanoffers = [Quest varIdX]
                                        }
                        , hiddenvars = Set.empty
                        , constraint = cstrConst (Cbool True)
            }

-- action: A?y
actOfferAy :: ActOffer
actOfferAy   = ActOffer {  offers = Set.singleton
                                        Offer { chanid = chanIdA
                                              , chanoffers = [Quest varIdY]
                                        }
                        , hiddenvars = Set.empty
                        , constraint = cstrConst (Cbool True)
            }

-- action: A!x
actOfferAExclamX :: ActOffer
actOfferAExclamX   = ActOffer {  offers = Set.singleton
                                        Offer { chanid = chanIdA
                                              , chanoffers = [Exclam vexprX]
                                        }
                        , hiddenvars = Set.empty
                        , constraint = cstrConst (Cbool True)
            }

-- action: B?x
actOfferBx :: ActOffer
actOfferBx   = ActOffer {  offers = Set.singleton
                                        Offer { chanid = chanIdB
                                              , chanoffers = [Quest varIdX]
                                        }
                        , hiddenvars = Set.empty
                        , constraint = cstrConst (Cbool True)
            }

-- action: B!x
actOfferBExclamX :: ActOffer
actOfferBExclamX   = ActOffer {  offers = Set.singleton
                              Offer { chanid = chanIdB
                                    , chanoffers = [Exclam vexprX]
                              }
                              , hiddenvars = Set.empty
                              , constraint = cstrConst (Cbool True)
            }

-- sorts, chanIds
intSort :: SortId
intSort = Maybe.fromMaybe (error "LPE module: could not find standard IntSort") (Map.lookup (T.pack "Int") stdSortTable)

chanIdA :: ChanId
chanIdA = ChanId    { ChanId.name = T.pack "A"
                    , ChanId.unid = 2
                    , ChanId.chansorts = [intSort]
                    }

chanIdA0 :: ChanId
chanIdA0 = ChanId    { ChanId.name = T.pack "A"
                        , ChanId.unid = 2
                        , ChanId.chansorts = []
}      

chanIdB :: ChanId
chanIdB = ChanId    { ChanId.name = T.pack "B"
                    , ChanId.unid = 3
                    , ChanId.chansorts = [intSort]
                    }
                  
anyInt :: VExpr
anyInt = cstrConst $ Cany intSort

