------------------------------------------------------------------------------
-- Test the consistency of Draft.FOTC.Data.Stream.Bisimilarity
------------------------------------------------------------------------------

-- In the module Draft.FOTC.Data.Stream.Bisimilarity we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module Draft.FOTC.Data.Stream.Bisimilarity.ConsistencyTest where

open import FOTC.Base

open import Draft.FOTC.Data.Stream.Bisimilarity

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
