------------------------------------------------------------------------------
-- Properties of the recursive operator rec
------------------------------------------------------------------------------

module LTC-PCF.DataPCF.NatPCF.RecPCF.PropertiesPCF where

open import LTC.Minimal
open import LTC-PCF.DataPCF.NatPCF.RecPCF using ( rec )

------------------------------------------------------------------------------
postulate
  rec-0 : (a : D){f : D} → rec zero a f ≡ a
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180 sec).
{-# ATP prove rec-0 #-}

postulate
  rec-S : (n a f : D) → rec (succ n) a f ≡ f ∙ n ∙ (rec n a f)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180 sec).
{-# ATP prove rec-S #-}
