------------------------------------------------------------------------------
-- Totality properties of the division
------------------------------------------------------------------------------

module LTC-PCF.Program.Division.TotalityATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.EquationsATP
open import LTC-PCF.Program.Division.Specification

------------------------------------------------------------------------------
-- The division is total when the dividend is less than the divisor.
postulate
  div-x<y-N : ∀ {i j} → LT i j → N (div i j)
{-# ATP prove div-x<y-N div-x<y #-}

-- The division is total when the dividend is greater or equal than
-- the divisor.

--  N (div (i ∸ j) j)       i ≮j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

postulate
  div-x≮y-N : ∀ {i j} →
              (DIV (i ∸ j) j (div (i ∸ j) j)) →
              NLT i j →
              N (div i j)
{-# ATP prove div-x≮y-N div-x≮y #-}
