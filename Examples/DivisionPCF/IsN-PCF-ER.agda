------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.DivisionPCF.IsN-PCF-ER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.DivisionPCF
open import Examples.DivisionPCF.EquationsPCF-ER
open import Examples.DivisionPCF.SpecificationPCF

open import LTC.Data.NatPCF
open import LTC.Data.NatPCF.InequalitiesPCF
open import LTC.Relation.Equalities.PropertiesER

------------------------------------------------------------------------------

-- The division result is a 'N' when the dividend is less than the divisor.
div-x<y-N : {i j : D} -> LT i j → N (div i j)
div-x<y-N i<j = subst (λ t → N t ) (sym (div-x<y i<j )) zN

-- The division result is a 'N' when the dividend is greater or equal
-- than the divisor.

--  N (div (i - j) j)       i ≥j → div i j ≡ succ (div (i - j) j)
------------------------------------------------------------------
--                   N (div i j)

div-x≥y-N : {i j : D} →
            (ih : DIV (i - j) j (div (i - j) j)) →
            GE i j →
            N (div i j)
div-x≥y-N ih i≥j = subst (λ t → N t ) (sym (div-x≥y i≥j )) (sN (∧-proj₁ ih ))
