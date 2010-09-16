------------------------------------------------------------------------------
-- Test the consistency of Examples.GCD.GCD
------------------------------------------------------------------------------

module Test.Consistency.Examples.GCD.GCD where

open import LTC.Minimal

open import Examples.GCD.GCD

------------------------------------------------------------------------------

postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}
