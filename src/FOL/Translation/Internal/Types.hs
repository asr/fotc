------------------------------------------------------------------------------
-- Translation from Agda *internal* types to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Internal.Types
    ( argTypeToFormula
    , typeToFormula
    )
    where

------------------------------------------------------------------------------
-- Haskell imports

-- import Control.Monad.IO.Class ( liftIO )
-- import Control.Monad.Trans.Class ( lift )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
    ( Arg(Arg, argHiding, unArg)
    , Hiding(Hidden, Instance, NotHidden)
    )
import Agda.Syntax.Internal  ( Sort(Type) , Term(Lit), Type(El) )
import Agda.Syntax.Literal   ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import FOL.Translation.Internal.Terms ( termToFormula )
import FOL.Types                      ( FOLFormula )
import Monad.Base                     ( T )
import Monad.Reports                  ( reportSLn )

#include "../../../undefined.h"

------------------------------------------------------------------------------

-- We keep the three equations for debugging.
argTypeToFormula ∷ Arg Type → T FOLFormula
argTypeToFormula Arg {argHiding = Instance}              = __IMPOSSIBLE__
argTypeToFormula Arg {argHiding = Hidden}                = __IMPOSSIBLE__
argTypeToFormula Arg {argHiding = NotHidden, unArg = ty} = typeToFormula ty

typeToFormula ∷ Type → T FOLFormula
typeToFormula ty@(El (Type (Lit (LitLevel _ n))) term)
    | n `elem` [0,1] = do
        reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
        termToFormula term
    | otherwise = __IMPOSSIBLE__
typeToFormula _ = __IMPOSSIBLE__
