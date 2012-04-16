------------------------------------------------------------------------------
-- |
-- Module      : Utils.Names
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities on names.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.Names ( freshName ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>=), (>>), fail) )
#endif
import Control.Monad ( Monad(return) )

import Control.Monad.State ( MonadState(get, put), State )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Function ( ($) )
import Data.List     ( (++), elem, map )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

#include "../undefined.h"

------------------------------------------------------------------------------

chars ∷ String
chars = ['a'..'z']

-- The set of free names for variables (a, b, ..., aa, ab, ...).
freeNames ∷ [String]
freeNames = map (:[]) chars ++ [ s ++ [c] | s ← freeNames, c ← chars ]

findFreeName ∷ [String] → [String] → String
findFreeName _         []       = __IMPOSSIBLE__
findFreeName usedNames (x : xs) =
  if x `elem` usedNames then findFreeName usedNames xs else x

-- | Generate a fresh name.
freshName ∷ State [String] String
freshName = do
  names ← get
  let newName ∷ String
      newName = findFreeName names freeNames
  put $ newName : names
  return newName
