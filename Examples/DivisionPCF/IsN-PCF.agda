------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.DivisionPCF.IsN-PCF where

open import LTC.Minimal

open import Examples.DivisionPCF
open import Examples.DivisionPCF.EquationsPCF
open import Examples.DivisionPCF.SpecificationPCF

open import LTC.Data.NatPCF
open import LTC.Data.NatPCF.InequalitiesPCF

------------------------------------------------------------------------------

-- The division result is a 'N' when the dividend is less than the divisor.
postulate
  div-x<y-N : {i j : D} -> LT i j → N (div i j)
{-# ATP prove div-x<y-N div-x<y zN #-}

-- The division result is a 'N' when the dividend is greater or equal
-- than the divisor.

--  N (div (i - j) j)       i ≥j → div i j ≡ succ (div (i - j) j)
------------------------------------------------------------------
--                   N (div i j)

postulate
  div-x≥y-N : {i j : D} → N i → N j →
              (DIV (i - j) j (div (i - j) j)) →
              GE i j →
              N (div i j)
{-# ATP prove div-x≥y-N div-x≥y sN #-}
