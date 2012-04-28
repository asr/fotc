------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Program.Division.EquationsATP where

open import Draft.FO-LTC-PCF.Base
open import Draft.FO-LTC-PCF.Data.Nat
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities
open import Draft.FO-LTC-PCF.Program.Division.Division

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor.
postulate div-x<y : ∀ {i j} → LT i j → div i j ≡ zero
{-# ATP prove div-x<y #-}

-- The division result when the dividend is greater or equal than the
-- the divisor.
postulate div-x≮y : ∀ {i j} → NLT i j → div i j ≡ succ₁ (div (i ∸ j) j)
{-# ATP prove div-x≮y #-}
