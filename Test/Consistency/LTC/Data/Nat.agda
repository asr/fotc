------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Nat
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Nat where

open import LTC.Minimal

open import LTC.Data.Nat

------------------------------------------------------------------------------
postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}
