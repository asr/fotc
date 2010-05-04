------------------------------------------------------------------------------
-- Inequalities on partial natural numbers
------------------------------------------------------------------------------

module LTC.Relation.Inequalities where

open import LTC.Minimal
open import MyStdLib.Data.Product

------------------------------------------------------------------------------

postulate
  lt : D → D → D

  lt-00 : lt zero zero                     ≡ false

  lt-0S : (d : D) → lt zero (succ d)       ≡ true

  lt-S0 : (d : D) → lt (succ d) zero       ≡ false

  lt-SS : (d e : D) → lt (succ d) (succ e) ≡ lt d e

{-# ATP axiom lt-00 #-}
{-# ATP axiom lt-0S #-}
{-# ATP axiom lt-S0 #-}
{-# ATP axiom lt-SS #-}

gt : D → D → D
gt d e = lt e d
{-# ATP definition gt #-}

------------------------------------------------------------------------
-- The data types

-- infix 4 _≤_ _<_ _≥_ _>_

GT : D → D → Set
GT d e = gt d e ≡ true
{-# ATP definition GT #-}

LT : D → D  → Set
LT d e = lt d e ≡ true
{-# ATP definition LT #-}

LE : D → D → Set
LE d e = gt d e ≡ false
{-# ATP definition LE #-}

GE : D → D → Set
GE d e = lt d e ≡ false
{-# ATP definition GE #-}

-- ------------------------------------------------------------------------
-- -- Lexicographical order on D
-- data LT₂ : D × D → D × D → Set where
--   left  : {x₁ x₂ y₁ y₂ : D} → LT x₁ x₂ → LT₂ (x₁ , y₁) (x₂ , y₂)
--   right : {x y₁ y₂ : D} →  LT y₁ y₂ → LT₂ (x , y₁) (x , y₂)
-- -- {-# ATP hint left #-}
-- -- {-# ATP hint right #-}
