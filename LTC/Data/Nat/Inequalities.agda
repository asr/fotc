------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

module LTC.Data.Nat.Inequalities where

open import LTC.Minimal

------------------------------------------------------------------------------

postulate
  lt    : D → D → D

  lt-00 : lt zero zero                     ≡ false

  lt-0S : (d : D) → lt zero (succ d)       ≡ true

  lt-S0 : (d : D) → lt (succ d) zero       ≡ false

  lt-SS : (d e : D) → lt (succ d) (succ e) ≡ lt d e

{-# ATP axiom lt-00 #-}
{-# ATP axiom lt-0S #-}
{-# ATP axiom lt-S0 #-}
{-# ATP axiom lt-SS #-}

le : D → D → D
le d e = lt d (succ e)
{-# ATP definition le #-}

gt : D → D → D
gt d e = lt e d
{-# ATP definition gt #-}

ge : D → D → D
ge d e = le e d
{-# ATP definition ge #-}

------------------------------------------------------------------------
-- The data types

-- infix 4 _≤_ _<_ _≥_ _>_

GT : D → D → Set
GT d e = gt d e ≡ true
{-# ATP definition GT #-}

NGT : D → D → Set
NGT d e = gt d e ≡ false
{-# ATP definition NGT #-}

LT : D → D → Set
LT d e = lt d e ≡ true
{-# ATP definition LT #-}

NLT : D → D → Set
NLT d e = lt d e ≡ false
{-# ATP definition NLT #-}

LE : D → D → Set
LE d e = le d e ≡ true
{-# ATP definition LE #-}

NLE : D → D → Set
NLE d e = le d e ≡ false
{-# ATP definition NLE #-}

GE : D → D → Set
GE d e = ge d e ≡ true
{-# ATP definition GE #-}

NGE : D → D → Set
NGE d e = ge d e ≡ false
{-# ATP definition NGE #-}

------------------------------------------------------------------------------
-- The lexicographical order
LT₂ : D → D → D → D → Set
LT₂ x₁ y₁ x₂ y₂ = LT x₁ x₂ ∨ x₁ ≡ x₂ ∧ LT y₁ y₂
{-# ATP definition LT₂ #-}

