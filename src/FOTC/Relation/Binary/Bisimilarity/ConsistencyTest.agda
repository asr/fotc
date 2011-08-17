------------------------------------------------------------------------------
-- Test the consistency of FOTC.Relation.Binary.Bisimilarity
------------------------------------------------------------------------------

-- In the module FOTC.Relation.Binary.Bisimilarity we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Relation.Binary.Bisimilarity.ConsistencyTest where

open import FOTC.Base

open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
