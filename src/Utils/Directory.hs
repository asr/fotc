------------------------------------------------------------------------------
-- |
-- Module      : Utils.Directory
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities on directories.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Directory ( diff ) where

------------------------------------------------------------------------------
-- Haskell imports

import Data.Algorithm.Diff ( DI(F, S), getDiff )

------------------------------------------------------------------------------

-- | The function 'diff' returns 'True' if the files are different,
-- otherwise the function returns 'False'.
diff ∷ FilePath → FilePath → IO Bool
diff f1 f2 = do

  l1 ← readFile f1
  l2 ← readFile f2

  let di ∷ [DI]
      di = fst $ unzip $ getDiff l1 l2

  if F `elem` di || S `elem` di then return True else return False
