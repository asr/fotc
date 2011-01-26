------------------------------------------------------------------------------
-- The LTC booleans type
------------------------------------------------------------------------------

module LTC.Data.Bool.Type where

open import LTC.Base

------------------------------------------------------------------------------
-- The LTC booleans type.
data Bool : D → Set where
  tB : Bool true
  fB : Bool false
{-# ATP hint tB #-}
{-# ATP hint fB #-}

-- The rule of proof by case analysis on Bool.
indBool : (P : D → Set) → P true → P false → ∀ {b} → Bool b → P b
indBool P pt pf tB = pt
indBool P pt pf fB = pf
