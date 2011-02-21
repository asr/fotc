------------------------------------------------------------------------------
-- The McCarthy 91 function
------------------------------------------------------------------------------

module FOTC.Program.McCarthy91.McCarthy91 where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

-- The McCarthy 91 function.
postulate
  mc91     : D → D
  mc91-eq₁ : ∀ n → GT n one-hundred → mc91 n ≡ n ∸ ten
  mc91-eq₂ : ∀ n → LE n one-hundred → mc91 n ≡ mc91 (mc91 (n + eleven))
{-# ATP axiom mc91-eq₁ #-}
{-# ATP axiom mc91-eq₂ #-}
