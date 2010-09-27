------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Nat.Inequalities where

open import LTC.Minimal

open import LTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}

