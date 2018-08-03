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
import qualified EnvData
import Control.Monad.State
import TxsDefs
import ProcId
import ChanId
import SortId
import qualified Data.Text         as T
import VarId
import ConstDefs
import ValExpr
import Sigs

import qualified Config
import qualified EnvCore as IOC
import qualified ParamCore
import qualified Solve.Params

import LPEOps
import LPEConstElm

initializeEnvC :: IOC.EnvC
initializeEnvC = IOC.EnvC { IOC.config = initConfig
                          , IOC.unid   = 0
                          , IOC.params = Config.updateParamVals initParams $ Config.configuredParameters initConfig
                          , IOC.state  = initState
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

constElmFunc :: LPEInstance -> IO (Maybe LPEInstance)
constElmFunc lpeInstance = evalStateT (constElm lpeInstance) initializeEnvC

testConstElm :: Test
testConstElm = TestCase $ do
    maybeResult <- constElmFunc lpeInstance
    case maybeResult of
      Just _result -> assertBool "True" (lpeInstance==lpeInstance)
      _ -> assertBool "output of constElm is valid" False
  where
    summand1 :: LPESummand
    summand1 = LPESummand
        [(chanIdA, [varIdZ])]
        (cstrEqual vexprZ vexpr0)
        [(varIdX, vexpr1), (varIdY, vexpr0)]
    summand2 :: LPESummand
    summand2 = LPESummand
        [(chanIdA, [varIdY])]
        (cstrAnd (Set.fromList [cstrEqual vexprX vexpr1, cstrEqual vexprY vexpr0]))
        [(varIdX, vexpr0), (varIdY, vexprY)]
    lpeInstance :: LPEInstance
    lpeInstance = ([chanIdA], [(varIdX, vexpr0), (varIdY, vexpr0)], [summand1, summand2])
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
intSort = SortId {  SortId.name = T.pack "Int"
                  , SortId.unid = 1}

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

