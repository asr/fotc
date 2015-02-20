------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Program.Division.Specification where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Specification: The division is total and the result is correct.
divSpec : D → D → D → Set
divSpec i j q = N q ∧ (∃[ r ] N r ∧ r < j ∧ i ≡ j * q + r)
