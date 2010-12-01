------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Bool
------------------------------------------------------------------------------

module Test.Consistency.LTC.Data.Bool.Impossible where

open import LTC.Base

open import LTC.Data.Bool

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
