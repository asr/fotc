------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Stream.Bisimilarity
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Stream.Bisimilarity.Impossible where

open import LTC.Base

open import LTC.Data.Stream.Bisimilarity

------------------------------------------------------------------------------
-- See Test.Consistency.README.txt
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
