------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.DivisionPCF.IsN-PCF where

open import LTC.Minimal

open import Examples.DivisionPCF.DivisionPCF using ( div )
open import Examples.DivisionPCF.EquationsPCF using ( div-x<y ; div-x≥y )
open import Examples.DivisionPCF.SpecificationPCF using ( DIV )

open import LTC-PCF.DataPCF.NatPCF
  using ( _-_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( GE ; LT )

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
-- Metis 2.3 (release 20100920) no-success due to timeout (180).
{-# ATP prove div-x≥y-N div-x≥y sN #-}
