------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.IsN-ATP where

open import LTC.Base

open import LTC-PCF.Data.Nat
  using ( _∸_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Inequalities using ( GE ; LT )

open import LTC-PCF.Program.Division.Division using ( div )
open import LTC-PCF.Program.Division.EquationsATP using ( div-x<y ; div-x≥y )
open import LTC-PCF.Program.Division.Specification using ( DIV )

------------------------------------------------------------------------------
-- The division result is a 'N' when the dividend is less than the divisor.
postulate
  div-x<y-N : ∀ {i j} → LT i j → N (div i j)
{-# ATP prove div-x<y-N div-x<y zN #-}

-- The division result is a 'N' when the dividend is greater or equal
-- than the divisor.

--  N (div (i ∸ j) j)       i ≥j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

postulate
  div-x≥y-N : ∀ {i j} → N i → N j →
              (DIV (i ∸ j) j (div (i ∸ j) j)) →
              GE i j →
              N (div i j)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove div-x≥y-N div-x≥y sN #-}
