------------------------------------------------------------------------------
-- Well-founded induction on the lexicographic order on N
------------------------------------------------------------------------------

module LTC.Data.N.Induction.Lexicographic where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Data.N.Postulates using ( wellFoundedLT )
open import LTC.Relation.Inequalities

import MyStdLib.Induction.Lexicographic
open module LexicographicLT₂ = MyStdLib.Induction.Lexicographic LT LT
open import MyStdLib.Induction.WellFounded

------------------------------------------------------------------------------

wellFoundedInd-N₂ :
  (P : D × D → Set) →
  ((mn : D × D) →
       (( op : D × D) → LT₂ op mn → N₂ op → P op) →
       N₂ mn → P mn) →
  {mn : D × D } → N₂ mn → P mn
wellFoundedInd-N₂ P accH {mn} =
  wellFoundedInd {D × D}
                 {LT₂}
                 {λ xy → N₂ xy → P xy}
                 (wellFoundedLexi wellFoundedLT wellFoundedLT)
                 accH
                 mn
