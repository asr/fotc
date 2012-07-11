------------------------------------------------------------------------------
-- Test the consistency of FOTC.Relation.Binary.Bisimilarity
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Relation.Binary.Bisimilarity we declare Agda
-- postulates as first-order logic axioms. We test if it is possible
-- to prove an unprovable theorem from these axioms.

module FOTC.Relation.Binary.Bisimilarity.ConsistencyTest where

open import FOTC.Base
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
