------------------------------------------------------------------------------
-- Example of a partial function using the Bove-Capretta method
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001.

module FOT.FOTC.Program.Min.MinBC-SL where

open import Data.Nat renaming ( suc to succ )
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

data minAcc : (ℕ → ℕ) → Set where
  minacc0 : (f : ℕ → ℕ) → f 0 ≡ 0 → minAcc f
  minacc1 : (f : ℕ → ℕ) → f 0 ≢ 0 → minAcc (λ n → f (succ n)) → minAcc f

min : (f : ℕ → ℕ) → minAcc f → ℕ
min f (minacc0 .f q)   = 0
min f (minacc1 .f q h) = succ (min (λ n → f (succ n)) h)
