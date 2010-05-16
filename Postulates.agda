module Postulates where

open import LTC.Minimal

open import LTC.Data.N
-- open import LTC.Function.Arithmetic
open import LTC.Relation.Inequalities

open import MyStdLib.Induction.WellFounded

postulate
  wf-LT₂ : WellFounded₂ LT₂

postulate
  Sx≤y→x<y : {m n : D} → N m → N n → LE (succ m) n → LT m n
  x<y→Sx≤y : {m n : D} → N m → N n → LT m n → LE (succ m) n
  Sx≤Sy→x≤y : {m n : D} → N m → N n → LE (succ m) (succ n) → LE m n
  ≤-trans : {m n o : D} → N m → N n → N o → LE m n → LE n o → LE m o
