------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

open import LTC-PCF.Program.Division.Division

open import LTC-PCF.Fix.Properties  -- Required to use the fix-f hint.

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor.
postulate div-x<y : ∀ {i j} → LT i j → div i j ≡ zero
{-# ATP prove div-x<y #-}

-- The division result when the dividend is greater or equal than the
-- the divisor.
postulate div-x≮y : ∀ {i j} → NLT i j → div i j ≡ succ₁ (div (i ∸ j) j)
{-# ATP prove div-x≮y #-}
