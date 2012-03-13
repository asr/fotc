------------------------------------------------------------------------------
-- The FOTC Booleans type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Bool.

module FOTC.Data.Bool.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC Booleans type (inductive predicate for total Booleans).
data Bool : D → Set where
  tB : Bool true
  fB : Bool false
{-# ATP axiom tB fB #-}

-- The rule of proof by case analysis.
Bool-ind : (A : D → Set) → A true → A false → ∀ {b} → Bool b → A b
Bool-ind A At Af tB = At
Bool-ind A At Af fB = Af
