------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

module LTC.Data.Nat.Inequalities where

open import LTC.Base

------------------------------------------------------------------------------

postulate
  _<_  : D → D → D
  <-00 :             zero   < zero   ≡ false
  <-0S : (d : D) →   zero   < succ d ≡ true
  <-S0 : (d : D) →   succ d < zero   ≡ false
  <-SS : (d e : D) → succ d < succ e ≡ d < e

{-# ATP axiom <-00 #-}
{-# ATP axiom <-0S #-}
{-# ATP axiom <-S0 #-}
{-# ATP axiom <-SS #-}

_≤_ : D → D → D
d ≤ e = d < succ e
{-# ATP definition _≤_ #-}

_>_ : D → D → D
d > e = e < d
{-# ATP definition _>_ #-}

_≥_ : D → D → D
_≥_ d e = e ≤ d
{-# ATP definition _≥_ #-}

------------------------------------------------------------------------
-- The data types

GT : D → D → Set
GT d e = d > e ≡ true
{-# ATP definition GT #-}

NGT : D → D → Set
NGT d e = d > e ≡ false
{-# ATP definition NGT #-}

LT : D → D → Set
LT d e = d < e ≡ true
{-# ATP definition LT #-}

NLT : D → D → Set
NLT d e = d < e ≡ false
{-# ATP definition NLT #-}

LE : D → D → Set
LE d e = d ≤ e ≡ true
{-# ATP definition LE #-}

NLE : D → D → Set
NLE d e = d ≤ e ≡ false
{-# ATP definition NLE #-}

GE : D → D → Set
GE d e = d ≥ e ≡ true
{-# ATP definition GE #-}

NGE : D → D → Set
NGE d e = d ≥ e ≡ false
{-# ATP definition NGE #-}

------------------------------------------------------------------------------
-- The lexicographical order.
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
{-# ATP definition LT₂ #-}
