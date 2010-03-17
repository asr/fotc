{-# LANGUAGE CPP #-}

module Names where

-- Haskell imports
import Control.Monad.Reader ( ask, local )

-- Agda library imports
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import Monad ( T )

#include "undefined.h"

------------------------------------------------------------------------------

-- The set of free names for variables (a, b, ..., aa, ab, ...).
chars :: String
chars = ['a'..'z']

freeNames :: [String]
freeNames = map (:[]) chars ++ [ s ++ [c] | s <- freeNames, c <- chars ]

findFreeName :: [String] -> [String] -> String
findFreeName _         []     = __IMPOSSIBLE__
findFreeName usedNames (x:xs) = if x `elem` usedNames
                                 then findFreeName usedNames xs
                                 else x
freshVar :: T String
freshVar = do
  (_, vars) <- ask
  return $ findFreeName vars freeNames

bindVar :: String -> T a -> T a
bindVar name = local $ \(o, vars) -> (o, name : vars)
