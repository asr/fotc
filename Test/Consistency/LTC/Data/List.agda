------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.List
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.List where

open import LTC.Base

open import LTC.Data.List

------------------------------------------------------------------------------
-- See Test.Consistency.Readme.
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
