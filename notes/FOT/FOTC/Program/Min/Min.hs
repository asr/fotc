{-# LANGUAGE UnicodeSyntax #-}

-- From (Bove, A. and Capretta, V. (2001).

import Data.Peano
import Prelude hiding ( min )

-- Note (25 December 2013): The @otherwise@ guard is required for
-- avoiding a non-exhaustive pattern matching warning. See
-- https://ghc.haskell.org/trac/ghc/ticket/29.
min ∷ (Nat → Nat) → Nat
min f | f 0 == 0  = 0
      | f 0 /= 0  = S (min (\n → f (S n)))
      | otherwise = error "min impossible"

------------------------------------------------------------------------------
-- References
--
-- Bove, A. and Capretta, V. (2001). Nested General Recursion and
-- Partiality in Type Theory. In: Theorem Proving in Higher Order
-- Logics (TPHOLs 2001). Ed. by Boulton, R. J. and Jackson,
-- P. B. Vol. 2152. LNCS. Springer, pp. 121–135.
