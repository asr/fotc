------------------------------------------------------------------------------
-- The division specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Program.Division.Specification where

open import Draft.FO-LTC-PCF.Base
open import Draft.FO-LTC-PCF.Data.Nat
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- The division is total and the result is correct.
DIV : D → D → D → Set
DIV i j q = N q ∧ (∃[ r ] N r ∧ LT r j ∧ i ≡ j * q + r)
{-# ATP definition DIV #-}
