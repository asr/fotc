{-# LANGUAGE UnicodeSyntax #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001.

import Prelude hiding ( min )

-- TODO. 04 December 2012. Why it is necessary to add the otherwise
-- guard?
min ∷ (Int → Int) → Int
min f | f 0 == 0  = 0
      | f 0 /= 0  = min (\n → f (n + 1)) + 1
      | otherwise = error "Impossible"
