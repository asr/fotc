------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.List
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.List.Impossible where

open import LTC.Base

open import LTC.Data.List

------------------------------------------------------------------------------
-- See Test.Consistency.README.txt.
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
