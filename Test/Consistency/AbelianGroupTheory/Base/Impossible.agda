------------------------------------------------------------------------------
-- Test the consistency of AbelianGroupTheory.Base
------------------------------------------------------------------------------

module Test.Consistency.AbelianGroupTheory.Base.Impossible where

open import AbelianGroupTheory.Base

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
