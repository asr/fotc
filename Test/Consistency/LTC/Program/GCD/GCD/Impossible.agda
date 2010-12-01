------------------------------------------------------------------------------
-- Test the consistency of LTC.Program.GCD.GCD
------------------------------------------------------------------------------

module Test.Consistency.LTC.Program.GCD.GCD.Impossible where

open import LTC.Base

open import LTC.Program.GCD.GCD

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
