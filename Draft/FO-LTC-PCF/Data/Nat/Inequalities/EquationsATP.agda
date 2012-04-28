------------------------------------------------------------------------------
-- Equations for the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Data.Nat.Inequalities.EquationsATP where

open import Draft.FO-LTC-PCF.Base
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------

postulate <-00 : NLT zero zero
{-# ATP prove <-00 #-}

postulate <-0S : ∀ n → LT zero (succ₁ n)
{-# ATP prove <-0S #-}

postulate <-S0 : ∀ n → NLT (succ₁ n) zero
{-# ATP prove <-S0 #-}

postulate <-SS : ∀ m n → succ₁ m < succ₁ n ≡ m < n
{-# ATP prove <-SS #-}
