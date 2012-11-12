------------------------------------------------------------------------------
-- Totality properties of the division
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Division.TotalityATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.Division.Division
open import FOTC.Program.Division.Specification

------------------------------------------------------------------------------
-- The division is total when the dividend is less than the divisor.
postulate div-x<y-N : ∀ {i j} → i < j → N (div i j)
{-# ATP prove div-x<y-N #-}

-- The division is total when the dividend is greater or equal than
-- the divisor.

--  N (div (i ∸ j) j)       i ≮j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

postulate
  div-x≮y-N : ∀ {i j} →
              (DIV (i ∸ j) j (div (i ∸ j) j)) →
              i ≮ j →
              N (div i j)
{-# ATP prove div-x≮y-N #-}
