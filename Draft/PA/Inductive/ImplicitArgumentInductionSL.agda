------------------------------------------------------------------------------
-- Testing an implicit argument for natural numbers induction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on 19 May 2012.

module ImplicitArgumentInductionSL where

open import Data.Nat renaming ( suc to succ )
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

succ-cong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succ-cong refl = refl

-- TODO: 19 May 2012. Why we cannot use an implicit argument in the
-- inductive hypothesis?

ℕ-ind : (A : ℕ → Set) → A zero → (∀ {n} → A n → A (succ n)) → ∀ n → A n
ℕ-ind A A0 h zero     = A0
ℕ-ind A A0 h (succ n) = h (ℕ-ind A A0 h n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc m n o = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≡ i + (n + o)

  A0 : A zero
  A0 = refl

  is : ∀ {i} → A i → A (succ i)
  is ih = succ-cong ih
