{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
{-# LANGUAGE OverloadedStrings #-}
module Benchmarks.LPEBakery (benchmarksSet) where

import           Benchmarks.Common
import           Paths
import           Prelude           hiding (FilePath)
import           Sqatt
import qualified Data.Text as Text

benchDir :: FilePath
benchDir = "LPE"

coreName :: String
coreName = "BakeryModel"

example1 :: TxsExample
example1 = emptyExample
    { exampleName = "Unchanged" ++ coreName
    , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack ("Unchanged" ++ coreName)) ]
    , txsCmdsFiles = [ seedSetupCmdFile, txsCmdPath BenchTest benchDir "Test" ]
    , expectedResult = Pass
    }

example2 :: TxsExample
example2 = emptyExample
    { exampleName = "Reduced" ++ coreName
    , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack ("Reduced" ++ coreName)) ]
    , txsCmdsFiles = [ seedSetupCmdFile, txsCmdPath BenchTest benchDir "Test" ]
    , expectedResult = Pass
    }

benchmarksSet :: TxsExampleSet
benchmarksSet = TxsExampleSet (fromString ("LPE" ++ coreName)) [ example1, example2 ]


