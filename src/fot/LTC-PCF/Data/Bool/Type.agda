------------------------------------------------------------------------------
-- The LTC-PCF Booleans type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by LTC-Bool.Data.Bool.

module LTC-PCF.Data.Bool.Type where

open import LTC-PCF.Base

------------------------------------------------------------------------------
-- The LTC-PCF Booleans type (inductive predicate for total Booleans).
data Bool : D → Set where
  btrue : Bool true
  bfalse : Bool false

-- The rule of proof by case analysis.
Bool-ind : (A : D → Set) → A true → A false → ∀ {b} → Bool b → A b
Bool-ind A At Af btrue  = At
Bool-ind A At Af bfalse = Af
