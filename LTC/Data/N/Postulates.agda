module LTC.Data.N.Postulates where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Relation.Inequalities

------------------------------------------------------------------------
-- Well-founded induction on pairs of 'N'

postulate
 wf₂-indN :
    (P : D → D → Set) →
    ({m n : D} → N m → N n →
        ({m' n' : D} → N m' → N n' → LT₂ (m' , n') (m , n) → P m' n')
          → P m n
    ) →
    {m n : D} → N m → N n → P m n
