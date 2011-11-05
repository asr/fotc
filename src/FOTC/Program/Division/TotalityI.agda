------------------------------------------------------------------------------
-- Totality properties of the division
------------------------------------------------------------------------------

module FOTC.Program.Division.TotalityI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.Division.Division
open import FOTC.Program.Division.EquationsI
open import FOTC.Program.Division.Specification

------------------------------------------------------------------------------
-- The division is total when the dividend is less than the divisor.
div-x<y-N : ∀ {i j} → LT i j → N (div i j)
div-x<y-N i<j = subst N (sym $ div-x<y i<j) zN

-- The division is total when the dividend is greater or equal than
-- the divisor.

--  N (div (i ∸ j) j)       i ≮ j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

div-x≮y-N : ∀ {i j} →
            (ih : DIV (i ∸ j) j (div (i ∸ j) j)) →
            NLT i j →
            N (div i j)
div-x≮y-N ih i≮j = subst N (sym $ div-x≮y i≮j) (sN (∧-proj₁ ih))
