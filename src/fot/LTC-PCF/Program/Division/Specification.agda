------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.Division.Specification where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- The division is total and the result is correct.
DIV : D → D → D → Set
DIV i j q = N q ∧ (∃[ r ] N r ∧ r < j ∧ i ≡ j * q + r)
