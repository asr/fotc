------------------------------------------------------------------------------
-- Translation from Agda *internal* types to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Internal.Types ( typeToFormula ) where

------------------------------------------------------------------------------
-- Haskell imports
-- import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Internal ( Sort(Type) , Term(Lit), Type(El) )
import Agda.Syntax.Literal ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

------------------------------------------------------------------------------
-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Internal.Terms ( termToFormula )
import FOL.Types ( FormulaFOL )
import Reports ( reportSLn )

#include "../../../undefined.h"

------------------------------------------------------------------------------

typeToFormula :: Type -> T FormulaFOL
typeToFormula ty@(El (Type (Lit (LitLevel _ n))) term)
    | n `elem` [ 0, 1 ] = do
      lift $ lift $ reportSLn "typeToFormula" 10 $
                               "Processing type ty:\n" ++ show ty
      termToFormula term
    | otherwise = __IMPOSSIBLE__
typeToFormula _ = __IMPOSSIBLE__
