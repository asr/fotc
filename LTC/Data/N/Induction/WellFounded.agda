------------------------------------------------------------------------------
-- Well-founded induction on N
------------------------------------------------------------------------------

module LTC.Data.N.Induction.WellFounded where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Relation.Inequalities
open import MyStdLib.Induction.WellFounded
open import Postulates using ( wellFoundedLT )

------------------------------------------------------------------------------

wellFoundedInd-N :
   (P : D → Set) →
   ((x : D) → ((y : D) → LT y x → N y → P y ) → N x → P x ) →
   (n : D) → N n → P n
wellFoundedInd-N P accH n =
  wellFoundedInd {D} {LT} {λ x → N x → P x} wellFoundedLT accH n
