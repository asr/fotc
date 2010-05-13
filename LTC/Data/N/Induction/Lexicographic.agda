------------------------------------------------------------------------------
-- Well-founded induction on the lexicographic order on N
------------------------------------------------------------------------------

module LTC.Data.N.Induction.Lexicographic where

open import LTC.Minimal

open import LTC.Data.N
open import Postulates using ( wf-LT₂ )
open import LTC.Relation.Inequalities

open import MyStdLib.Induction.WellFounded

------------------------------------------------------------------------------

-- Well-founded induction on the lexicographic order on N.
wfInd-LT₂ :
  (P : D → D → Set) →
  ({m₁ n₁ : D} →
       ({m₂ n₂ : D} → LT₂ m₂ n₂ m₁ n₁ → N m₂ → N n₂ → P m₂ n₂) →
       N m₁ → N n₁ → P m₁ n₁ ) →
  {m n : D} → N m → N n → P m n
wfInd-LT₂ P accH = wfInd₂ {D} {LT₂} {λ x y → N x → N y → P x y} wf-LT₂ accH
