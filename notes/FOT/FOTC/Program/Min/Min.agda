------------------------------------------------------------------------------
-- Example of a partial function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001.

module FOT.FOTC.Program.Min.Min where

open import Data.Nat renaming ( suc to succ )
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

-- Note: Although the function is partial the problem is that it is
-- rejected by Agda's termination checker.

{-# NO_TERMINATION_CHECK #-}
min : (ℕ → ℕ) → ℕ
min f with f 0
... | 0      = 0
... | succ x = succ (min (λ n → f (succ n)))
