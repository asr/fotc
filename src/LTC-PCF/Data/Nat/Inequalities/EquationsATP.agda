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

postulate <-0S : ∀ d → LT zero (succ₁ d)
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-0S #-}

postulate <-S0 : ∀ d → NLT (succ₁ d) zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-S0 #-}

postulate <-SS : ∀ d e → succ₁ d < succ₁ e ≡ d < e
{-# ATP prove <-SS #-}
