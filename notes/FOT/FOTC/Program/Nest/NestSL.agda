------------------------------------------------------------------------------
-- Example of a nested recursive function using the standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001.

module FOT.FOTC.Program.Nest.NestSL where

open import Data.Nat renaming (suc to succ)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- The non-terminating function.
{-# NO_TERMINATION_CHECK #-}
nest : ℕ → ℕ
nest 0        = 0
nest (succ n) = nest (nest n)

-- The non-terminating property.
{-# NO_TERMINATION_CHECK #-}
nest-x≡0 : ∀ n → nest n ≡ zero
nest-x≡0 zero     = refl
nest-x≡0 (succ n) = nest-x≡0 (nest n)
