------------------------------------------------------------------------------
-- Totality properties of the division
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.Division.Totality where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Program.Division.ConversionRules
open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.Specification

------------------------------------------------------------------------------
-- The division is total when the dividend is less than the divisor.
div-x<y-N : ∀ {i j} → LT i j → N (div i j)
div-x<y-N i<j = subst N (sym (div-x<y i<j)) nzero

-- The division is total when the dividend is greater or equal than
-- the divisor.

--  N (div (i ∸ j) j)       i ≮ j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

div-x≮y-N : ∀ {i j} →
            (DIV (i ∸ j) j (div (i ∸ j) j)) →
            NLT i j →
            N (div i j)
div-x≮y-N ih i≮j = subst N (sym (div-x≮y i≮j)) (nsucc (∧-proj₁ ih))
