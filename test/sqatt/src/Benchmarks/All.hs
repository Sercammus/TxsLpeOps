{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}

module Benchmarks.All (allExamples, allBenchmarks) where

--import qualified Benchmarks.Choice          as Choice
--import qualified Benchmarks.Dynamic         as Dynamic
--import qualified Benchmarks.Enable          as Enable
--import qualified Benchmarks.Hiding          as Hiding
--import qualified Benchmarks.Parallel        as Parallel
--import qualified Benchmarks.LPEAdder3         as LPEAdder3
--import qualified Benchmarks.LPEBakery         as LPEBakery
--import qualified Benchmarks.LPEMAdder         as LPEMAdder
import qualified Benchmarks.LPEBenchmarkSets      as LPEBenchmarkSets
--import qualified Benchmarks.LPELuckyPeople    as LPELuckyPeople
--import qualified Benchmarks.Queue           as Queue
--import qualified Benchmarks.RealWorld       as RealWorld
--import qualified Benchmarks.Sequence        as Sequence
--import qualified Benchmarks.Synchronization as Synchronization
import           Criterion.Main
import           Sqatt

allExamples :: [TxsExampleSet]
allExamples = [ --Choice.benchmarksSet
              --, Dynamic.benchmarksSet
              --, Enable.benchmarksSet
              --, Hiding.benchmarksSet
              --, LPEMAdder.benchmarksSet
              LPEBenchmarkSets.lpeBenchmarkSet "AdderModel",
              LPEBenchmarkSets.lpeBenchmarkSet "Adder3Model",
              LPEBenchmarkSets.lpeBenchmarkSet "MAdderModel",
              LPEBenchmarkSets.lpeBenchmarkSet "BakeryModel",
              --LPEBenchmarkSets.lpeBenchmarkSet "CustomersOrdersModel", -- Does not terminate!
              LPEBenchmarkSets.lpeBenchmarkSet "EchoModel",
              LPEBenchmarkSets.lpeBenchmarkSet "EchoDelayModel",
              LPEBenchmarkSets.lpeBenchmarkSet "EchoLPEModel",
              LPEBenchmarkSets.lpeBenchmarkSet "PointModel",
              LPEBenchmarkSets.lpeBenchmarkSet "QueueModel",
              LPEBenchmarkSets.lpeBenchmarkSet "LossyQueueModel",
              LPEBenchmarkSets.lpeBenchmarkSet "ReadWriteModel"
              --, RealWorld.benchmarksSet
              --, Sequence.benchmarksSet
              --, Synchronization.benchmarksSet
              --Queue.benchmarksSet
              ]

allBenchmarks :: [Benchmark]
allBenchmarks = benchmarkExampleSet <$> allExamples
