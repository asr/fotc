------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities where

open import LTC-PCF.Base

------------------------------------------------------------------------------
-- Version using lambda-abstraction.
lth : D → D
lth lt = lam (λ m → lam (λ n →
              if (iszero₁ n) then false
                 else (if (iszero₁ m) then true
                          else (lt · (pred₁ m) · (pred₁ n)))))
_<_ : D → D → D
m < n = fix lth · m · n

_≤_ : D → D → D
m ≤ n = m < succ₁ n

_>_ : D → D → D
m > n = n < m

_≥_ : D → D → D
m ≥ n = n ≤ m

------------------------------------------------------------------------
-- The data types

GT : D → D → Set
GT m n = m > n ≡ true

NGT : D → D → Set
NGT m n = m > n ≡ false

LT : D → D → Set
LT m n = m < n ≡ true

NLT : D → D → Set
NLT m n = m < n ≡ false

LE : D → D → Set
LE m n = m ≤ n ≡ true

NLE : D → D → Set
NLE m n = m ≤ n ≡ false

GE : D → D → Set
GE m n = m ≥ n ≡ true

NGE : D → D → Set
NGE m n = m ≥ n ≡ false

------------------------------------------------------------------------------
-- The lexicographical order.
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
