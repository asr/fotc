------------------------------------------------------------------------------
-- Conversion rules for the division
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Division.ConversionRules where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Program.Division.Division

----------------------------------------------------------------------

-- NB. These equations are not used by the ATPs. They use the official
-- equation.
private
  -- The division result when the dividend is minor than the
  -- the divisor.
  postulate div-x<y : ∀ {i j} → i < j → div i j ≡ zero
  {-# ATP prove div-x<y #-}

  -- The division result when the dividend is greater or equal than the
  -- the divisor.
  postulate div-x≮y : ∀ {i j} → i ≮ j → div i j ≡ succ₁ (div (i ∸ j) j)
  {-# ATP prove div-x≮y #-}
