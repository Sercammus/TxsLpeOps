{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
{-# LANGUAGE FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  TorXakis.Compiler.ValExpr.CstrDef
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
--
-- Maintainer  :  damian.nadales@gmail.com (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Compilation functions related to 'TorXakis' constructor definitions.
--------------------------------------------------------------------------------
module TorXakis.Compiler.ValExpr.CstrDef
    (compileToCstrDefs)
where

import           Data.Map                         (Map)
import qualified Data.Map                         as Map

import           CstrDef                          (CstrDef (CstrDef))
import           CstrId                           (CstrId (CstrId))

import           TorXakis.Compiler.Data           (CompilerM)
import           TorXakis.Compiler.MapsTo         (MapsTo, lookupM)
import           TorXakis.Compiler.ValExpr.FuncId (cstrToIsCstrFuncId)
import           TorXakis.Parser.Data             (ADTDecl, CstrDecl, CstrE,
                                                   Loc, constructors,
                                                   getLoc)

-- | Compile a list of ADT declarations into a map from constructor id's to
-- their definitions.
compileToCstrDefs :: ( MapsTo (Loc CstrE) CstrId mm )
                  => mm -> [ADTDecl] -> CompilerM (Map CstrId CstrDef)
compileToCstrDefs mm ds =
    Map.fromList . concat <$> traverse (adtToCstrDefs mm) ds

-- | Compile an ADT declaration into a list constructor id's and
-- constructor definition pairs.
adtToCstrDefs :: ( MapsTo (Loc CstrE) CstrId mm )
               => mm -> ADTDecl -> CompilerM [(CstrId, CstrDef)]
adtToCstrDefs mm a =
    traverse (cstrToCstrDefs mm) (constructors a)

-- | Compile a constructor declaration into a list constructor id's and
-- constructor definition pairs.
cstrToCstrDefs :: ( MapsTo (Loc CstrE) CstrId mm )
               => mm -> CstrDecl -> CompilerM (CstrId, CstrDef)
cstrToCstrDefs mm c = do
    cId@(CstrId _ _ accessFids _) <- lookupM (getLoc c) mm
    isCstrFid <- cstrToIsCstrFuncId cId
    return (cId, CstrDef isCstrFid accessFids)
