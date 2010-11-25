------------------------------------------------------------------------------
-- Test the consistency of Examples.GroupTheory.Base
------------------------------------------------------------------------------

module Test.Consistency.Examples.GroupTheory.Base where

open import Examples.GroupTheory.Base

------------------------------------------------------------------------------

postulate
  impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
