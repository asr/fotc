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
import Agda.Syntax.Common
    ( Arg(Arg)
    , argHiding
    , Hiding(Hidden, NotHidden)
    , unArg
    )
import Agda.Syntax.Internal ( Sort(Type) , Type(El) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

------------------------------------------------------------------------------
-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Terms ( termToFormula )
import FOL.Types ( FormulaFOL )
import Reports ( reportLn )

#include "../../undefined.h"

------------------------------------------------------------------------------

type AgdaType = Type

typeToFormula :: AgdaType -> T FormulaFOL
typeToFormula ty@(El (Type _ ) term) =
    do lift $ reportLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
       termToFormula term
typeToFormula _                   = __IMPOSSIBLE__

argTypeToFormula :: Arg AgdaType -> T FormulaFOL
argTypeToFormula Arg {argHiding = NotHidden, unArg = ty} = typeToFormula ty
argTypeToFormula Arg {argHiding = Hidden} =
    error "argTypeToFormula: not implemented"
