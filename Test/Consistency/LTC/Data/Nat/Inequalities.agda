------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Nat.Inequalities where

open import LTC.Base

open import LTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- See Test.Consistency.Readme.
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
