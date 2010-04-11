------------------------------------------------------------------------------
-- Translation from Agda types to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Types where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.Trans.Class ( lift )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Common ( Arg(Arg) )
import Agda.Syntax.Internal ( Sort(Type) , Type(El) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

------------------------------------------------------------------------------
-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Common ( AgdaType )
import FOL.Translation.Terms ( termToFormula )
import FOL.Types ( FormulaFOL )
import Reports ( reportSLn )

#include "../../undefined.h"

------------------------------------------------------------------------------

typeToFormula :: AgdaType -> T FormulaFOL
typeToFormula ty@(El (Type _ ) term) =
    do lift $ reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
       termToFormula term
typeToFormula _                   = __IMPOSSIBLE__

argTypeToFormula :: Arg AgdaType -> T FormulaFOL
argTypeToFormula (Arg _ ty) = typeToFormula ty
