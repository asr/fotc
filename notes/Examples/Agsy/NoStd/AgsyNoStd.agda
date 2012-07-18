------------------------------------------------------------------------------
-- Testing Agsy *without* use the Agda standard library
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 15 June 2012.

module Examples.Agsy.NoStd.AgsyNoStd where

-- The equational reasoning from the standard library.
-- open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning

-- My equational reasoning.
open import Examples.Agsy.NoStd.MyPropositionalEquality
open ≡-Reasoning

-- We add 3 to the fixities of the standard library.
infixl 9 _+_

------------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero    n o = refl  -- via Agsy
+-assoc (suc m) n o = {!!}  -- Agsy fails using my propositional equality
