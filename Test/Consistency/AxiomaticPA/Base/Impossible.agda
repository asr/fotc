------------------------------------------------------------------------------
-- Test the consistency of AxiomaticPA.Base
------------------------------------------------------------------------------

module Test.Consistency.AxiomaticPA.Base.Impossible where

open import AxiomaticPA.Base

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (m n : ℕ) → m ≡ n
{-# ATP prove impossible #-}
