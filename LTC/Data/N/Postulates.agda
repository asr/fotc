module LTC.Data.N.Postulates where

open import LTC.Relation.Inequalities

open import MyStdLib.Induction.WellFounded
import MyStdLib.Induction.Lexicographic
open module PostulatesLT₂ = MyStdLib.Induction.Lexicographic LT LT

------------------------------------------------------------------------

postulate
  wellFoundedLT : WellFounded LT
