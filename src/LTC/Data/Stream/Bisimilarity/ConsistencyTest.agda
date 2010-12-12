------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Stream.Bisimilarity
------------------------------------------------------------------------------

-- In the module LTC.Data.Stream.Bisimilarity we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module LTC.Data.Stream.Bisimilarity.ConsistencyTest where

open import LTC.Base

open import LTC.Data.Stream.Bisimilarity

------------------------------------------------------------------------------

postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
