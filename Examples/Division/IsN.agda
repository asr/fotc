------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module Examples.Division.IsN where

open import LTC.Minimal

open import Examples.Division
open import Examples.Division.Equations
open import Examples.Division.Specification

open import LTC.Data.N
open import LTC.Function.ArithmeticPCF
open import LTC.Relation.InequalitiesPCF

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
  div-x≥y-N : {i j : D} →
              (DIV (i - j) j (div (i - j) j)) →
              GE i j →
              N (div i j)
{-# ATP prove div-x≥y-N div-x≥y sN #-}
