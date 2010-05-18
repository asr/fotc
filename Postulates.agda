module Postulates where

open import LTC.Minimal

open import LTC.Data.N
-- open import LTC.Function.Arithmetic
open import LTC.Relation.Inequalities

open import MyStdLib.Induction.WellFounded

postulate
  wf-LT₂ : WellFounded₂ LT₂

postulate
  Sx≤Sy→x≤y : {m n : D} → N m → N n → LE (succ m) (succ n) → LE m n
