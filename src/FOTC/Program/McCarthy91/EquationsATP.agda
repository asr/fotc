------------------------------------------------------------------------------
-- Equations for the McCarthy 91 function
------------------------------------------------------------------------------

module FOTC.Program.McCarthy91.EquationsATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

open import FOTC.Program.McCarthy91.McCarthy91

------------------------------------------------------------------------------

postulate
  mc91-eq₁ : ∀ n → GT n one-hundred → mc91 n ≡ n ∸ ten
  mc91-eq₂ : ∀ {n} → N n → LE n one-hundred → mc91 n ≡ mc91 (mc91 (n + eleven))
{-# ATP prove mc91-eq₁ mc91-eq #-}
{-# ATP prove mc91-eq₂ mc91-eq x≤y→x≯y 100-N #-}
