------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.DivisionPCF.IsN-PCF-ER where

open import LTC.Base
open import LTC.BaseER using ( subst )

open import Examples.DivisionPCF.DivisionPCF using ( div )
open import Examples.DivisionPCF.EquationsPCF-ER  using ( div-x<y ; div-x≥y )
open import Examples.DivisionPCF.SpecificationPCF using ( DIV )

open import LTC-PCF.DataPCF.NatPCF
  using ( _-_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( GE ; LT )

------------------------------------------------------------------------------
-- The division result is a 'N' when the dividend is less than the divisor.
div-x<y-N : {i j : D} -> LT i j → N (div i j)
div-x<y-N i<j = subst N (sym (div-x<y i<j)) zN

-- The division result is a 'N' when the dividend is greater or equal
-- than the divisor.

--  N (div (i - j) j)       i ≥j → div i j ≡ succ (div (i - j) j)
------------------------------------------------------------------
--                   N (div i j)

div-x≥y-N : {i j : D} → N i → N j →
            (ih : DIV (i - j) j (div (i - j) j)) →
            GE i j →
            N (div i j)
div-x≥y-N Ni Nj ih i≥j = subst N (sym (div-x≥y Ni Nj i≥j)) (sN (∧-proj₁ ih))
