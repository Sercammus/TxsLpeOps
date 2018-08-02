module ShowBExpr(
showBExpr
) where

import BehExprDefs
import qualified TxsShow
import qualified TxsDefs

showBExpr :: BExpr -> String
showBExpr bexpr = TxsShow.fshow $ TxsDefs.view bexpr
