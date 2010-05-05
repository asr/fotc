------------------------------------------------------------------------------
-- Well-founded induction on the lexicographic order on N
------------------------------------------------------------------------------

module LTC.Data.N.Induction.Lexicographic where

open import LTC.Minimal

open import LTC.Data.N
open import Postulates using ( wellFoundedLT )
open import LTC.Relation.Inequalities

import MyStdLib.Induction.Lexicographic
open module LexicographicLT₂ = MyStdLib.Induction.Lexicographic LT LT
open import MyStdLib.Induction.WellFounded

------------------------------------------------------------------------------

-- Well-founded induction on the lexicographic order on N.
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

-- A version without use the data type N₂.
wellFoundedInd-N₂' :
  (P : D × D → Set) →
  ((mn : D × D) →
       (( op : D × D) → LT₂ op mn → N (×-proj₁ op) → N (×-proj₂ op) → P op) →
       N (×-proj₁ mn) → N (×-proj₂ mn) → P mn) →
  {mn : D × D } → N (×-proj₁ mn) → N (×-proj₂ mn) → P mn
wellFoundedInd-N₂' P accH {mn} =
  wellFoundedInd {D × D}
                 {LT₂}
                 {λ xy → N (×-proj₁ xy) → N (×-proj₂ xy) → P xy}
                 (wellFoundedLexi wellFoundedLT wellFoundedLT)
                 accH
                 mn
