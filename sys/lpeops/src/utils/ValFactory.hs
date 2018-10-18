{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ValFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ValFactory (
sort2defaultValue
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified ValExpr
import qualified SortId
import qualified Constant
import qualified CstrId

sort2defaultValue :: TxsDefs.TxsDefs -> SortId.SortId -> TxsDefs.VExpr
sort2defaultValue tdefs sortId
    | sortId == SortId.sortIdBool =
        (ValExpr.cstrConst (Constant.Cbool False))
    | sortId == SortId.sortIdInt =
        (ValExpr.cstrConst (Constant.Cint 0))
    | sortId == SortId.sortIdString =
        (ValExpr.cstrConst (Constant.Cstring (Text.pack "")))
    | sortId == SortId.sortIdRegex =
        (ValExpr.cstrConst (Constant.Cstring (Text.pack "")))
    | otherwise =
        -- Use any non-recursive constructor of this sort to express a value of this sort:
        case [ cstrId | cstrId <- Map.keys (TxsDefs.cstrDefs tdefs), CstrId.cstrsort cstrId == sortId, not(isRecursiveCstr tdefs cstrId) ] of
          (cstrId:_) -> ValExpr.cstrCstr cstrId (map (sort2defaultValue tdefs) (CstrId.cstrargs cstrId))
          [] -> error ("Failed to generate a default value for " ++ show sortId ++ " (available={" ++ (List.intercalate ", " (map show (Map.keys (TxsDefs.cstrDefs tdefs)))) ++ "})!")
-- sort2defaultValue

isRecursiveCstr :: TxsDefs.TxsDefs -> CstrId.CstrId -> Bool
isRecursiveCstr tdefs cstrId = List.or (map (isRecursiveSort tdefs Set.empty) (CstrId.cstrargs cstrId))
-- isRecursiveCstr

isRecursiveSort :: TxsDefs.TxsDefs -> Set.Set SortId.SortId -> SortId.SortId -> Bool
isRecursiveSort tdefs beenHere sortId
    | sortId == SortId.sortIdBool = False
    | sortId == SortId.sortIdInt = False
    | sortId == SortId.sortIdString = False
    | sortId == SortId.sortIdRegex = False
    | otherwise =
        let sortCstrs = [ cstrId | cstrId <- Map.keys (TxsDefs.cstrDefs tdefs), CstrId.cstrsort cstrId == sortId ] in
        let sortCstrParamSorts = concat (map CstrId.cstrargs sortCstrs) in
          (Set.member sortId beenHere) || (List.or (map (isRecursiveSort tdefs (Set.insert sortId beenHere)) sortCstrParamSorts))
-- isRecursiveSort



