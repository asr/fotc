------------------------------------------------------------------------------
-- Conversion rules for the recursive operator rec
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Rec.EquationsATP where

open import LTC.Base

open import LTC-PCF.Data.Nat.Rec using ( rec )

------------------------------------------------------------------------------

postulate
  rec-0 : (a : D){f : D} → rec zero a f ≡ a
{-# ATP prove rec-0 #-}

postulate
  rec-S : (n a f : D) → rec (succ n) a f ≡ f · n · (rec n a f)
-- Equinox 5.0alpha (2010-06-29) no-success due to timeout (180 sec).
{-# ATP prove rec-S #-}
