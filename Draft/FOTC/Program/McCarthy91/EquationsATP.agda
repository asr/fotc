------------------------------------------------------------------------------
-- Equations for the McCarthy 91 function
------------------------------------------------------------------------------

module Draft.FOTC.Program.McCarthy91.EquationsATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

postulate
  mc91 : D → D
  mc91-eq : ∀ n → mc91 n ≡ if (n > one-hundred)
                             then n ∸ ten
                             else mc91 (mc91 (n + eleven))
{-# ATP axiom mc91-eq #-}

postulate
  mc91-eq₁ : ∀ {n} → N n → GT n one-hundred → mc91 n ≡ n ∸ ten
  mc91-eq₂ : ∀ {n} → N n → LE n one-hundred → mc91 n ≡ mc91 (mc91 (n + eleven))
{-# ATP prove mc91-eq₁ #-}
{-# ATP prove mc91-eq₂ x≤y→x≯y 100-N #-}
