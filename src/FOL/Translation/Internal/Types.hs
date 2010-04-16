------------------------------------------------------------------------------
-- Translation from Agda *internal* types to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Internal.Types where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.Trans.Class ( lift )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Internal ( Sort(Type) , Term(Lit), Type(El) )
import Agda.Syntax.Literal ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

------------------------------------------------------------------------------
-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Common ( AgdaType )
import FOL.Translation.Internal.Terms ( termToFormula )
import FOL.Types ( FormulaFOL )
import Reports ( reportSLn )

#include "../../../undefined.h"

------------------------------------------------------------------------------

typeToFormula :: AgdaType -> T FormulaFOL
typeToFormula ty@(El (Type (Lit (LitLevel _ n))) term)
    | n == 0 || n == 1 = do
       lift $ reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
       termToFormula term
    | otherwise = __IMPOSSIBLE__
typeToFormula _ = __IMPOSSIBLE__
