{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  MCRL2ProcDefs
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module MCRL2Defs (
ObjectId,
Sort(..),
Constructor(..),
DExpr(..),
Variable(..),
VariableEq,
VariableEqs,
Action(..),
MultiAction,
AInstance(..),
AExpr(..),
PExpr(..),
Equation(..),
EquationGroup(..),
Process(..),
Specification(..),
emptySpecification
) where

import qualified Data.Map as Map
import qualified Data.Text as Text

type ObjectId = Text.Text

data Sort = BoolSort
          | IntSort
          | ListSort Sort
          | SetSort Sort
          | BagSort Sort
          | StructSort [Constructor]
          | SortRef ObjectId
          | MultiSort Sort Sort
          | FunctionSort Sort Sort
          | ImplicitSort
          | MissingMapping
          | MissingSort
        deriving (Eq)
-- Sort

data Constructor = Constructor { cstrName :: ObjectId
                               , fields :: [Variable]
                               , recognizer :: ObjectId
                               } | MissingConstructor
                             deriving (Eq)
-- Constructor

data DExpr = DBool Bool
           | DInt Integer
           | DList [DExpr]
           | DFiniteSet [DExpr]
           | DVariableRef Variable
           | DConstructorRef ObjectId VariableEqs
           | DRecognizer ObjectId DExpr
           | DFieldAccess ObjectId DExpr
           | DMappingRef ObjectId [DExpr]
           | DEqual DExpr DExpr
           | DNotEqual DExpr DExpr
           | DGreaterEquals DExpr DExpr
           | DSmallerEquals DExpr DExpr
           | DAnd DExpr DExpr
           | DOr DExpr DExpr
           | DIfThenElse DExpr DExpr DExpr
           | DNot DExpr
           | DAdd DExpr DExpr
           | DSubtract DExpr DExpr
           | DMultiply DExpr DExpr
           | DDivide DExpr DExpr
           | DModulo DExpr DExpr
           | DListSize DExpr
           | DListElement DExpr DExpr
           | DListConcatenate DExpr DExpr
-- DExpr

data Variable = Variable { varName :: ObjectId, varSort :: Sort } | MissingVariable
                       deriving (Eq)

type VariableEq = (Variable, DExpr)
type VariableEqs = [VariableEq]

data Action = Action [Sort] | MissingAction
type MultiAction = [ObjectId]

data AInstance = AInstance ObjectId [DExpr]
data AExpr = ATau | AExpr [AInstance]

data PExpr = PAction AExpr
           | PSeq [PExpr]
           | PPar [PExpr]
           | PChoice [PExpr]
           | PSum [Variable] PExpr
           | PGuard DExpr PExpr PExpr
           | PDeadlock
           | PAllow [MultiAction] PExpr
           | PHide [ObjectId] PExpr
           | PComm [(MultiAction, ObjectId)] PExpr
           | PRename [(ObjectId, ObjectId)] PExpr
           | PBlock [ObjectId] PExpr
           | PInst ObjectId VariableEqs
-- PExpr

data Equation = Equation { lhs :: DExpr, rhs :: DExpr }
data EquationGroup = EquationGroup { variables :: [Variable], equations :: [Equation] }

data Process = Process { processParams :: [Variable], expr :: PExpr } | MissingProcess

data Specification = Specification { sorts :: Map.Map ObjectId Sort
                                   , mappings :: Map.Map ObjectId Sort
                                   , equationGroups :: [EquationGroup]
                                   , actions :: Map.Map ObjectId Action
                                   , processes :: Map.Map ObjectId Process
                                   , globals :: Map.Map ObjectId Variable
                                   , init :: PExpr
                                   }
-- Specification

emptySpecification :: MCRL2Defs.Specification
emptySpecification = MCRL2Defs.Specification { MCRL2Defs.sorts = Map.empty
                                             , MCRL2Defs.mappings = Map.empty
                                             , MCRL2Defs.equationGroups = []
                                             , MCRL2Defs.actions = Map.empty
                                             , MCRL2Defs.processes = Map.empty
                                             , MCRL2Defs.globals = Map.empty
                                             , MCRL2Defs.init = MCRL2Defs.PDeadlock
                                             }
-- emptySpecification


