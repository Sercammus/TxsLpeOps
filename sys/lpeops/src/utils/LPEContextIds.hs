{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEContextIds
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module LPEContextIds (
getModelIds,
getProcessIds,
getSummandIds,
getValExprIds
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified FuncId
import qualified CstrId
import qualified SortOf
import qualified ChanId
import qualified FuncDef
import qualified VarId
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           LPETypeDefs
import           ValExprVisitor
import           Ident

-- Because Set.unions does not work on sets of sets for some reason?
setUnions :: (Foldable f, Ord a) => f (Set.Set a) -> Set.Set a
setUnions = foldl Set.union Set.empty

getModelIds :: LPEModel -> Set.Set Ident
getModelIds (tdefs, process) =
    untilFixpoint (getProcessIds process)
  where
    untilFixpoint :: Set.Set Ident -> Set.Set Ident
    untilFixpoint currentIds =
      let nextIds = getNextIds currentIds in
        if nextIds == currentIds
        then currentIds
        else untilFixpoint nextIds
    -- untilFixpoint
    
    getNextIds :: Set.Set Ident -> Set.Set Ident
    getNextIds currentIds =
      let funcIds = setUnions (Set.map getFuncId currentIds) in
      let funcDefs = Set.map getFuncDef funcIds in
      let recursiveIds = setUnions (Set.map getFuncIds funcDefs) in
        Set.union currentIds recursiveIds
    -- getNextIds
    
    getFuncId :: Ident -> Set.Set FuncId.FuncId
    getFuncId (IdFunc fid) = Set.singleton fid
    getFuncId _ = Set.empty
    
    getFuncDef :: FuncId.FuncId -> FuncDef.FuncDef VarId.VarId
    getFuncDef fid = (TxsDefs.funcDefs tdefs) Map.! fid
    
    getFuncIds :: FuncDef.FuncDef VarId.VarId -> Set.Set Ident
    getFuncIds (FuncDef.FuncDef params body) = Set.union (getVarsIds params) (getValExprIds body)
-- getModelIds

-- Gathers all ids that are used in the given LPE process:
getProcessIds :: LPEProcess -> Set.Set Ident
getProcessIds (channels, initParamEqs, summands) =
    Set.unions [
      getChansIds channels,
      getParamEqsIds initParamEqs,
      setUnions (Set.map getSummandIds summands)
    ]
-- getProcessIds

-- Gathers all ids that are used in the given summand:
getSummandIds :: LPESummand -> Set.Set Ident
getSummandIds (LPESummand channelVars channelOffers guard paramEqs) =
    Set.unions [
      getVarsIds channelVars,
      getChansIds (map fst channelOffers),
      Set.unions (map (getVarsIds . snd) channelOffers),
      getValExprIds guard,
      getParamEqsIds paramEqs
    ]
-- getSummandIds

getParamEqsIds :: LPEParamEqs -> Set.Set Ident
getParamEqsIds =
    Set.unions . Map.elems . Map.mapWithKey getParamEqIds
  where
    getParamEqIds :: VarId.VarId -> TxsDefs.VExpr -> Set.Set Ident
    getParamEqIds var expr = Set.union (getVarIds var) (getValExprIds expr)
-- getParamEqsIds

-- Gathers all ids that are used in the given data expression:
getValExprIds :: TxsDefs.VExpr -> Set.Set Ident
getValExprIds = customData . visitValExpr searchVisitor
  where
    searchVisitor :: [ValExprVisitorOutput (Set.Set Ident)] -> TxsDefs.VExpr -> ValExprVisitorOutput (Set.Set Ident)
    searchVisitor subExps expr =
        let idsInSubExps = Set.unions (map customData subExps) in
        let ids = case expr of
                    (view -> Vconst (Cbool _))        -> idsInSubExps
                    (view -> Vconst (Cint _))         -> idsInSubExps
                    (view -> Vconst (Cstring _))      -> idsInSubExps
                    (view -> Vconst (Cregex _))       -> idsInSubExps
                    (view -> Vconst (Ccstr cid _))    -> Set.insert (IdSort (CstrId.cstrsort cid)) idsInSubExps
                    (view -> Vconst (Cany sid))       -> Set.insert (IdSort sid) idsInSubExps
                    (view -> Vvar vid)                -> Set.insert (IdVar vid) idsInSubExps
                    (view -> Vfunc fid _)             -> Set.insert (IdFunc fid) idsInSubExps
                    (view -> Vcstr cid _)             -> Set.insert (IdSort (CstrId.cstrsort cid)) idsInSubExps
                    (view -> Viscstr cid _)           -> Set.insert (IdSort (CstrId.cstrsort cid)) idsInSubExps
                    (view -> Vaccess cid _ _)         -> Set.insert (IdSort (CstrId.cstrsort cid)) idsInSubExps
                    (view -> Vite _ _ _)              -> idsInSubExps
                    (view -> Vdivide _ _)             -> idsInSubExps
                    (view -> Vmodulo _ _)             -> idsInSubExps
                    (view -> Vgez _)                  -> idsInSubExps
                    (view -> Vsum _)                  -> idsInSubExps
                    (view -> Vproduct _)              -> idsInSubExps
                    (view -> Vequal _ _)              -> idsInSubExps
                    (view -> Vand _)                  -> idsInSubExps
                    (view -> Vnot _)                  -> idsInSubExps
                    (view -> Vlength _)               -> idsInSubExps
                    (view -> Vat _ _)                 -> idsInSubExps
                    (view -> Vconcat _)               -> idsInSubExps
                    (view -> Vstrinre _ _)            -> idsInSubExps
                    (view -> Vpredef _ fid _)         -> Set.insert (IdFunc fid) idsInSubExps
                    _                                 -> error ("GetValExprIds.searchVisitor not defined for " ++ show expr ++ "!")
        in ValExprVisitorOutput expr 1 ids
    -- searchVisitor
-- getValExprIds

getChansIds :: [ChanId.ChanId] -> Set.Set Ident
getChansIds = Set.unions . map getChanIds

getChanIds :: ChanId.ChanId -> Set.Set Ident
getChanIds chan = Set.fromList (IdChan chan : map IdSort (ChanId.chansorts chan))

getVarsIds :: [VarId.VarId] -> Set.Set Ident
getVarsIds = Set.unions . map getVarIds

getVarIds :: VarId.VarId -> Set.Set Ident
getVarIds var = Set.fromList [IdVar var, IdSort (SortOf.sortOf var)]


