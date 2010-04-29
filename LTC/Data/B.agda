------------------------------------------------------------------------------
-- Inductive predicate for the total booleans
------------------------------------------------------------------------------

module LTC.Data.B where

open import LTC.Minimal

------------------------------------------------------------------------------

-- The LTC booleans type.
data B : D → Set where
  tB : B true
  fB : B false

-- The rule of proof by case analysis on 'B'.
indB : (P : D → Set) → P true → P false → {b : D} → B b → P b
indB P pt pf tB = pt
indB P pt pf fB = pf
