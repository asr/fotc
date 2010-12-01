------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.Base
------------------------------------------------------------------------------

module Test.Consistency.GroupTheory.Base.Impossible where

open import GroupTheory.Base

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
