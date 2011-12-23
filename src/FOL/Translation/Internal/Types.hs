------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Internal.Types
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation from Agda internal types to FOL formulas.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Internal.Types
  ( argTypeToFormula
  , typeToFormula
  ) where

------------------------------------------------------------------------------
-- Haskell imports

-- import Control.Monad.IO.Class ( liftIO )
-- import Control.Monad.Trans.Class ( lift )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Arg(Arg)
  , argHiding
  , Hiding(Hidden, Instance, NotHidden)
  , unArg
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
typeToFormula ty@(El (Type (Max [])) term) = do
  reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
  termToFormula term

typeToFormula ty@(El (Type (Max [ClosedLevel 1])) term) = do
    reportSLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
    termToFormula term

typeToFormula _ = __IMPOSSIBLE__
