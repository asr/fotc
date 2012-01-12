------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Internal.Types
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation from Agda internal types to FOL formulas.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Types
  ( argTypeToFormula
  , typeToFormula
  ) where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Arg(Arg, argHiding, unArg)
  , Hiding(Hidden, Instance, NotHidden)
  )

import Agda.Syntax.Internal
  ( Level(Max)
  , PlusLevel(ClosedLevel)
  , Sort(Type)
  , Type(El)
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import FOL.Translation.Terms ( termToFormula )
import FOL.Types             ( FOLFormula )
import Monad.Base            ( T )
import Monad.Reports         ( reportSLn )

#include "../../undefined.h"

------------------------------------------------------------------------------

-- | Translate an Agda internal Arg Type to a FOL formula.
argTypeToFormula ∷ Arg Type → T FOLFormula
argTypeToFormula Arg {argHiding = Instance}              = __IMPOSSIBLE__
argTypeToFormula Arg {argHiding = Hidden}                = __IMPOSSIBLE__
argTypeToFormula Arg {argHiding = NotHidden, unArg = ty} = typeToFormula ty

-- | Translate an Agda internal Type to a FOL formula.
typeToFormula ∷ Type → T FOLFormula
typeToFormula ty@(El (Type (Max [])) term) = do
  reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
  termToFormula term

typeToFormula ty@(El (Type (Max [ClosedLevel 1])) term) = do
  reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
  termToFormula term

typeToFormula _ = __IMPOSSIBLE__
