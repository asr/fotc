{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.Names ( freshName ) where

-- Haskell imports
-- import Control.Monad.Reader ( ask, Reader )
import Control.Monad.State ( get, put, State )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
-- import Monad ( T )

#include "../undefined.h"

------------------------------------------------------------------------------

chars ∷ String
chars = ['a'..'z']

-- The set of free names for variables (a, b, ..., aa, ab, ...).
freeNames ∷ [String]
freeNames = map (:[]) chars ++ [ s ++ [c] | s ← freeNames, c ← chars ]

findFreeName ∷ [String] → [String] → String
findFreeName _         []     = __IMPOSSIBLE__
findFreeName usedNames (x:xs) = if x `elem` usedNames
                                then findFreeName usedNames xs
                                else x

freshName ∷ State [String] String
freshName = do
  names ← get
  let newName ∷ String
      newName = findFreeName names freeNames
  put $ newName : names
  return newName

-- bindVar ∷ String → T a → T a
-- bindVar name = local $ \(o, vars) → (o, name : vars)
