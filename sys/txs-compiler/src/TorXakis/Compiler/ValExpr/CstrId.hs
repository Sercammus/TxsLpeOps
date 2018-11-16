{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
{-# LANGUAGE FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  TorXakis.Compiler.ValExpr.CstrId
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
--
-- Maintainer  :  damian.nadales@gmail.com (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Compilation functions related to 'TorXakis' constructor id's.
--------------------------------------------------------------------------------
module TorXakis.Compiler.ValExpr.CstrId
    (compileToCstrId)
where

import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Text                (Text)

import           CstrId                   (CstrId (CstrId))
import           Id                       (Id (Id))
import           SortId                   (SortId)
import           FuncId                   (FuncId (FuncId))

import           TorXakis.Compiler.Data   (CompilerM, getNextId)
import           TorXakis.Compiler.Maps   (findSortIdM)
import           TorXakis.Compiler.MapsTo (MapsTo)
import           TorXakis.Parser.Data     (ADTDecl, CstrDecl, CstrE,
                                           FuncDeclE, fieldName,
                                           Loc, Loc (PredefLoc),
                                           adtName, constructors, cstrFields,
                                           cstrName, fieldSort, getLoc, nodeLoc)

-- | Compile a list of ADT declarations into a map from the location of the
-- constructor declaration, to their corresponding constructor id's.
compileToCstrId :: (MapsTo Text SortId mm)
                => mm -> [ADTDecl] -> CompilerM (Map (Loc CstrE) CstrId, [((Loc FuncDeclE), FuncId)])
compileToCstrId mm ds = do
    cIds <- traverse (adtToCstrId mm) ds
    return (Map.fromList (concatMap fst cIds), concatMap snd cIds)

adtToCstrId :: (MapsTo Text SortId mm)
            => mm
            -> ADTDecl
            -> CompilerM ([(Loc CstrE, CstrId)], [(Loc FuncDeclE, FuncId)])
adtToCstrId mm a = do
    sId <- findSortIdM mm (adtName a, nodeLoc a)
    cIds <- traverse (cstrToCstrId mm sId) (constructors a)
    return ((map fst cIds), concatMap snd cIds)

cstrToCstrId :: (MapsTo Text SortId mm)
             => mm
             -> SortId -- ^ SortId of the containing ADT.
             -> CstrDecl
             -> CompilerM ((Loc CstrE, CstrId), [(Loc FuncDeclE, FuncId)])
cstrToCstrId mm sId c = do
    i <- getNextId
    accessFids <- traverse accessFdiFid (cstrFields c) -- Also create access functions here!
    return ((getLoc c, CstrId (cstrName c) (Id i) (map snd accessFids) sId), accessFids)
  where
    accessFdiFid f = do
      let accN = fieldName f
      accSid <- getNextId
      fSid   <- findSortIdM mm (fieldSort f)
      return (PredefLoc accN accSid, FuncId accN (Id accSid) [sId] fSid)
