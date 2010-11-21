------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module PCF.Examples.Division.Equations where

open import LTC.Base

open import PCF.Examples.Division.Division using ( div )

open import PCF.LTC.Data.Nat using ( _-_ ; N )
open import PCF.LTC.Data.Nat.Inequalities using ( GE ; LT )
open import PCF.LTC.Data.Nat.Inequalities.Properties
  using ( x≥y→x≮y )

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
