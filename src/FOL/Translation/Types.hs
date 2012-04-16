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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Types
  ( domTypeToFormula
  , typeToFormula
  ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>)) )
#endif

-- TODO: 2012-04-16. Why is it necessary?
#if __GLASGOW_HASKELL__ == 612
import Data.Eq ( Eq((==)) )
#endif

import Data.Function ( ($) )
import Data.List     ( (++) )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif

import Text.Show ( Show(show) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Dom(Dom, domHiding, unDom)
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
-- | Translate an Agda internal Dom Type to a FOL formula.
domTypeToFormula ∷ Dom Type → T FOLFormula
domTypeToFormula Dom {domHiding = Instance}              = __IMPOSSIBLE__
domTypeToFormula Dom {domHiding = Hidden}                = __IMPOSSIBLE__
domTypeToFormula Dom {domHiding = NotHidden, unDom = ty} = typeToFormula ty

-- | Translate an Agda internal Type to a FOL formula.
typeToFormula ∷ Type → T FOLFormula
typeToFormula ty@(El (Type (Max [])) term) = do
  reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
  termToFormula term

typeToFormula ty@(El (Type (Max [ClosedLevel 1])) term) = do
  reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
  termToFormula term

typeToFormula _ = __IMPOSSIBLE__
