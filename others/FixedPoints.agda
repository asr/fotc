{-# OPTIONS --universe-polymorphism #-}

module FixedPoints where

open import Level renaming ( zero to zeroL )

postulate
  D    : Set
  zero : D
  succ : D → D
  _≡_  : Set → Set → Set
  _≣_  : (D → Set) → (D → Set) → Set  -- Equality on predicates.

-- data _≡_ {l : Level}{A : Set l}(x : A) : A → Set l where
--   refl : x ≡ x

-- The pure (i.e. non-inductive) LTC natural numbers.
postulate
  N₁  : D → Set
  zN₁ : N₁ zero
  sN₁ : (n : D) → N₁ n → N₁ (succ n)

-- The LTC natural numbers.
data N₂ : D → Set where
  zN₂ : N₂ zero
  sN₂ : (n : D) → N₂ n → N₂ (succ n)

-- Because N₂ is an inductive data type, we can defined it as the least
-- fixed-point (Fix) of an appropriate functional.
postulate
  Fix  : ((D → Set) → D → Set) → D → Set
  cFix : (f : (D → Set) → D → Set) → Fix f ≣ f (Fix f)

-- A version of FN if D was an inductive type
-- FN : (D → Set) → D → Set
-- FN N zero     = N zero
-- FN N (succ n) = N n → N (succ N)

postulate
  FN     : (D → Set) → D → Set
  zeroFN : (N : D → Set) →        FN N zero     ≡ N zero
  succFN : (N : D → Set)(n : D) → FN N (succ n) ≡ N n → N (succ n)

-- The LTC natural numbers using Fix.
N₃ : D → Set
N₃ = Fix FN
