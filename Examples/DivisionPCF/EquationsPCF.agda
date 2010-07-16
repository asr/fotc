------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module Examples.DivisionPCF.EquationsPCF where

open import LTC.Minimal

open import Examples.DivisionPCF.DivisionPCF
open import LTC.Data.NatPCF
open import LTC.Data.NatPCF.InequalitiesPCF
open import LTC.Data.NatPCF.InequalitiesPCF.PropertiesPCF using ( x≥y→x≮y )

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor.
postulate
  div-x<y : {i j : D} → LT i j → div i j ≡ zero
{-# ATP prove div-x<y #-}

-- The division result when the dividend is greater or equal than the
-- the divisor.
postulate
  div-x≥y : {i j : D} → N i → N j → GE i j → div i j ≡ succ (div (i - j) j)
{-# ATP prove div-x≥y x≥y→x≮y #-}
