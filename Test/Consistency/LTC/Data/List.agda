------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.List
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.List where

open import LTC.Minimal
open import LTC.Data.List

------------------------------------------------------------------------------

postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}

