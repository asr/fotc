module Postulates where

open import LTC.Minimal

open import LTC.Data.N
-- open import LTC.Function.Arithmetic
open import LTC.Relation.Inequalities

open import MyStdLib.Induction.WellFounded

postulate
  wf-LT  : WellFounded LT
  wf-LT₂ : WellFounded₂ LT₂

postulate
  trans-LT : {m n o : D} → N m → N n → N o → LT m n → LT n o → LT m o
