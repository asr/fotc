{-# LANGUAGE UnicodeSyntax #-}

-- From (Bove, A. and Capretta, V. (2001).

import Data.Peano
import Prelude hiding ( min )

-- TODO (04 December 2012): Why it is necessary to add the otherwise
-- guard?
min ∷ (Nat → Nat) → Nat
min f | f 0 == 0  = 0
      | f 0 /= 0  = Succ (min (\n → f (Succ n)))
      | otherwise = error "min impossible"

------------------------------------------------------------------------------
-- References
--
-- Bove, A. and Capretta, V. (2001). Nested General Recursion and
-- Partiality in Type Theory. In: Theorem Proving in Higher Order
-- Logics (TPHOLs 2001). Ed. by Boulton, R. J. and Jackson,
-- P. B. Vol. 2152. LNCS. Springer, pp. 121–135.
