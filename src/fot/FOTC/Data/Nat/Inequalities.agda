------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities where

open import FOTC.Base

-- We add 4 to the fixities of the standard library.
infix 8 _<_ _≤_  _≥_ _>_

------------------------------------------------------------------------------

postulate
  _<_  : D → D → D
  <-00 : zero < zero               ≡ false
  <-0S : ∀ n → zero < succ₁ n      ≡ true
  <-S0 : ∀ n → succ₁ n < zero      ≡ false
  <-SS : ∀ m n → succ₁ m < succ₁ n ≡ m < n
{-# ATP axiom <-00 <-0S <-S0 <-SS #-}

_≤_ : D → D → D
m ≤ n = m < succ₁ n
{-# ATP definition _≤_ #-}

_>_ : D → D → D
m > n = n < m
{-# ATP definition _>_ #-}

_≥_ : D → D → D
m ≥ n = n ≤ m
{-# ATP definition _≥_ #-}

------------------------------------------------------------------------
-- The data types

GT : D → D → Set
GT m n = m > n ≡ true
{-# ATP definition GT #-}

NGT : D → D → Set
NGT m n = m > n ≡ false
{-# ATP definition NGT #-}

LT : D → D → Set
LT m n = m < n ≡ true
{-# ATP definition LT #-}

NLT : D → D → Set
NLT m n = m < n ≡ false
{-# ATP definition NLT #-}

LE : D → D → Set
LE m n = m ≤ n ≡ true
{-# ATP definition LE #-}

NLE : D → D → Set
NLE m n = m ≤ n ≡ false
{-# ATP definition NLE #-}

GE : D → D → Set
GE m n = m ≥ n ≡ true
{-# ATP definition GE #-}

NGE : D → D → Set
NGE m n = m ≥ n ≡ false
{-# ATP definition NGE #-}

------------------------------------------------------------------------------
-- The lexicographical order.
Lexi : D → D → D → D → Set
Lexi m₁ n₁ m₂ n₂ = LT m₁ m₂ ∨ m₁ ≡ m₂ ∧ LT n₁ n₂
{-# ATP definition Lexi #-}
