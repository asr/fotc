------------------------------------------------------------------------------
-- Equations for the inequalities
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Inequalities.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat.Inequalities

open import LTC-PCF.Fix.Properties  -- Required to use the hint fix-f.

------------------------------------------------------------------------------

postulate <-00 : NLT zero zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-00 fix-f #-}

postulate <-0S : ∀ d → LT zero (succ₁ d)
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-0S fix-f #-}

postulate <-S0 : ∀ d → NLT (succ₁ d) zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-S0 fix-f #-}

postulate <-SS : ∀ d e → succ₁ d < succ₁ e ≡ d < e
{-# ATP prove <-SS fix-f #-}
