------------------------------------------------------------------------------
-- Test the consistency of PA.Base
------------------------------------------------------------------------------

module Test.Consistency.PA.Base.Impossible where

open import PA.Base

------------------------------------------------------------------------------

postulate
  impossible : (m n : ℕ) → m ≡ n
{-# ATP prove impossible #-}
