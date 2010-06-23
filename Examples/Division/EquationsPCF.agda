------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module Examples.Division.EquationsPCF where

open import LTC.Minimal

open import Examples.DivisionPCF
open import LTC.Function.ArithmeticPCF
open import LTC.Relation.InequalitiesPCF

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor

postulate
  div-x<y : {i j : D} → LT i j → div i j ≡ zero
{-# ATP prove div-x<y #-}

-- The division result when the dividend is greater or equal than the
-- the divisor

postulate
  div-x≥y : {i j : D} → GE i j → div i j ≡ succ (div (i - j) j)
{-# ATP prove div-x≥y #-}
