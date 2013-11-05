------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Division.Specification where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Specification: The division is total and the result is correct.
divSpec : D → D → D → Set
divSpec i j q = N q ∧ (∃[ r ] N r ∧ r < j ∧ i ≡ j * q + r)
{-# ATP definition divSpec #-}
