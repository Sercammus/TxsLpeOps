{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}

module Main where

import System.Exit
import Test.HUnit

import TestConstElm
import TestParElm

testList :: Test
testList = TestList
    [
      TestLabel "constElmBasic"            testConstElmBasic
    , TestLabel "constElmXYX"              testConstElmXYX
    , TestLabel "parElmBasic"              testParElmBasic
    , TestLabel "testParElmXUpperBound"    testParElmXUpperBound
    ]

main :: IO ()
main = do
    Counts  _c _t e f <- runTestTT testList
    if 0 == e+f
    then exitSuccess
    else exitFailure
-- main

