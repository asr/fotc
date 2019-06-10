------------------------------------------------------------------------------
-- Totality properties of the division
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Division.Totality where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Program.Division.Division
open import Combined.FOTC.Program.Division.Specification

------------------------------------------------------------------------------
-- The division is total when the dividend is less than the divisor.
postulate div-x<y-N : ∀ {i j} → i < j → N (div i j)
{-# ATP prove div-x<y-N #-}

-- The division is total when the dividend is greater or equal than
-- the divisor.

--  N (div (i ∸ j) j)       i ≮j → div i j ≡ succ (div (i ∸ j) j)
------------------------------------------------------------------
--                   N (div i j)

postulate div-x≮y-N : ∀ {i j} →
                      (divSpec (i ∸ j) j (div (i ∸ j) j)) →
                      i ≮ j →
                      N (div i j)
{-# ATP prove div-x≮y-N #-}
