------------------------------------------------------------------------------
-- Utilities on directories
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Directory ( diff ) where

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
