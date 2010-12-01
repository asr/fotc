------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Nat
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Nat.Impossible where

open import LTC.Base

open import LTC.Data.Nat

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
