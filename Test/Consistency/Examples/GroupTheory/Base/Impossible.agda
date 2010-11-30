------------------------------------------------------------------------------
-- Test the consistency of Examples.GroupTheory.Base
------------------------------------------------------------------------------

module Test.Consistency.Examples.GroupTheory.Base.Impossible where

open import Examples.GroupTheory.Base

------------------------------------------------------------------------------
-- See Test.Consistency.README.txt
postulate
  impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
