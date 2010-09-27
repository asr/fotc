------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.List.Bisimulation
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.List.Bisimulation where

open import LTC.Minimal

open import LTC.Data.List.Bisimulation

------------------------------------------------------------------------------
postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}

