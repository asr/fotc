------------------------------------------------------------------------------
-- Test the consistency of Examples.GCD.GCD
------------------------------------------------------------------------------

module Test.Consistency.Examples.GCD.GCD.Impossible where

open import LTC.Base

open import Examples.GCD.GCD

------------------------------------------------------------------------------
-- See Test.Consistency.README.txt
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
