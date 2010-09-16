------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Bool
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Bool where

open import LTC.Minimal
open import LTC.Data.Bool

------------------------------------------------------------------------------

postulate
  impossible : ( d e : D) → d ≡ e
{-# ATP prove impossible #-}
