------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module FOTC.Program.Division.EquationsATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.Division.Division

----------------------------------------------------------------------

-- NB. These equations are not used by the ATPs. They use the official
-- equation.
private
  -- The division result when the dividend is minor than the
  -- the divisor.
  postulate div-x<y : ∀ {i j} → LT i j → div i j ≡ zero
  {-# ATP prove div-x<y #-}

  -- The division result when the dividend is greater or equal than the
  -- the divisor.
  postulate div-x≮y : ∀ {i j} → NLT i j → div i j ≡ succ₁ (div (i ∸ j) j)
  {-# ATP prove div-x≮y #-}
