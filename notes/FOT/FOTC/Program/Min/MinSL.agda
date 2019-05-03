------------------------------------------------------------------------------
-- Example of a partial function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

-- From (Bove, A. and Capretta, V. (2001)).

module FOT.FOTC.Program.Min.MinSL where

open import Data.Nat renaming ( suc to succ )
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Note: Although the function is partial the problem is that it is
-- rejected by Agda's termination checker.

{-# NON_TERMINATING #-}
min : (ℕ → ℕ) → ℕ
min f with f 0
... | 0      = 0
... | succ x = succ (min (λ n → f (succ n)))

------------------------------------------------------------------------------
-- References
--
-- Bove, A. and Capretta, V. (2001). Nested General Recursion and
-- Partiality in Type Theory. In: Theorem Proving in Higher Order
-- Logics (TPHOLs 2001). Ed. by Boulton, R. J. and Jackson,
-- P. B. Vol. 2152. LNCS. Springer, pp. 121–135.
