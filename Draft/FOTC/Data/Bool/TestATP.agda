------------------------------------------------------------------------------
-- Testing
------------------------------------------------------------------------------

module Draft.FOTC.Data.Bool.TestATP where

open import FOTC.Base

open import FOTC.Data.Bool.Type

------------------------------------------------------------------------------

postulate
  thm : ∀ {b}(P : D → Set) → (Bool b ∧ P true ∧ P false) → P b
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm #-}

postulate
  thm₁ : ∀ {P : D → Set}{x y z} → Bool x → P y → P z → P (if x then y else z)
-- The ATPs couldn't prove this postulate.
-- {-# ATP prove thm₁ #-}
