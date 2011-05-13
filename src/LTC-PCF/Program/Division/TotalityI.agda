------------------------------------------------------------------------------
-- Totality properties of the division
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.TotalityI where

open import LTC-PCF.Base

open import Common.Function

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.EquationsI
open import LTC-PCF.Program.Division.Specification

------------------------------------------------------------------------------
-- The division is total when the dividend is less than the divisor.
div-x<y-N : ∀ {i j} → LT i j → N (div i j)
div-x<y-N i<j = subst N (sym $ div-x<y i<j) zN

-- The division is total when the dividend is greater or equal than
-- the divisor.

--  N (div (i ∸ j) j)       i ≥j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

div-x≥y-N : ∀ {i j} → N i → N j →
            (ih : DIV (i ∸ j) j (div (i ∸ j) j)) →
            GE i j →
            N (div i j)
div-x≥y-N Ni Nj ih i≥j = subst N (sym $ div-x≥y Ni Nj i≥j) (sN (∧-proj₁ ih))
