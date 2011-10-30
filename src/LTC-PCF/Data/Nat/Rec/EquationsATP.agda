------------------------------------------------------------------------------
-- Conversion rules for the recursive operator rec
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Rec.EquationsATP where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat.Rec using ( rec )

open import LTC-PCF.Fix.Properties  -- Required to use the fix-f hint.

------------------------------------------------------------------------------

postulate rec-0 : ∀ a {f : D} → rec zero a f ≡ a
{-# ATP prove rec-0 #-}

postulate rec-S : ∀ n a (f : D) → rec (succ₁ n) a f ≡ f · n · (rec n a f)
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove rec-S #-}
