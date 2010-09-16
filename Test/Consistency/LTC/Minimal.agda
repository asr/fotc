------------------------------------------------------------------------------
-- Test the consistency of LTC.Minimal
------------------------------------------------------------------------------

module Test.Consistency.LTC.Minimal where

open import LTC.Minimal

------------------------------------------------------------------------------

postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}
