------------------------------------------------------------------------------
-- Test the consistency of LTC.Base
------------------------------------------------------------------------------

module Test.Consistency.LTC.Base where

open import LTC.Base

------------------------------------------------------------------------------
-- See Test.Consistency.Readme.
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
