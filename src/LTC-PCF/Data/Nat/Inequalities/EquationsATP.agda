------------------------------------------------------------------------------
-- Equations for the inequalities
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Inequalities.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat.Inequalities using ( _<_ ; LT ; NLT )

------------------------------------------------------------------------------

postulate <-00 : NLT zero zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-00 #-}

postulate <-0S : ∀ d → LT zero (succ d)
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-0S #-}

postulate <-S0 : ∀ d → NLT (succ d) zero
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove <-S0 #-}

postulate <-SS : ∀ d e → succ d < succ e ≡ d < e
{-# ATP prove <-SS #-}
