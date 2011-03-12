------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat using ( _∸_ ; N )
open import LTC-PCF.Data.Nat.Inequalities using ( GE ; LT )
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
  using ( x≥y→x≮y )

open import LTC-PCF.Program.Division.Division using ( div )

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor.
postulate
  div-x<y : ∀ {i j} → LT i j → div i j ≡ zero
{-# ATP prove div-x<y #-}

-- The division result when the dividend is greater or equal than the
-- the divisor.

-- Because we define GE on terms of LT, we need the extra hypotheses
-- N i and N j.
postulate
  div-x≥y : ∀ {i j} → N i → N j → GE i j → div i j ≡ succ (div (i ∸ j) j)
{-# ATP prove div-x≥y x≥y→x≮y #-}
