------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Division.Specification where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Specification: The division is total and the result is correct.
divSpec : D → D → D → Set
divSpec i j q = N q ∧ (∃[ r ] N r ∧ r < j ∧ i ≡ j * q + r)
