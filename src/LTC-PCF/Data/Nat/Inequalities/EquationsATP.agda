------------------------------------------------------------------------------
-- Equations for the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities.EquationsATP where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------

postulate <-00 : NLT zero zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-00 #-}

postulate <-0S : ∀ n → LT zero (succ₁ n)
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-0S #-}

postulate <-S0 : ∀ n → NLT (succ₁ n) zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-S0 #-}

postulate <-SS : ∀ m n → succ₁ m < succ₁ n ≡ m < n
{-# ATP prove <-SS #-}
