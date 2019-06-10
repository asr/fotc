------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Division.Specification where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Specification: The division is total and the result is correct.
divSpec : D → D → D → Set
divSpec i j q = N q ∧ (∃[ r ] N r ∧ r < j ∧ i ≡ j * q + r)
{-# ATP definition divSpec #-}
