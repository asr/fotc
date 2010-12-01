------------------------------------------------------------------------------
-- Test the consistency of LTC.Base
------------------------------------------------------------------------------

module Test.Consistency.LTC.Base.Impossible where

open import LTC.Base

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
