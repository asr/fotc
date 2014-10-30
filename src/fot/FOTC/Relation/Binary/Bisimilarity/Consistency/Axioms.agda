------------------------------------------------------------------------------
-- Test the consistency of FOTC.Relation.Binary.Bisimilarity.Type
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module FOTC.Relation.Binary.Bisimilarity.Type we declare
-- Agda postulates as first-order logic axioms. We test if it is
-- possible to prove unprovable theorems from these axioms.

module FOTC.Relation.Binary.Bisimilarity.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}

postulate ≡→≈ : ∀ {xs ys} → xs ≡ ys → xs ≈ ys
{-# ATP prove ≡→≈ #-}

postulate ≈→≡ : ∀ {xs ys} → xs ≈ ys → xs ≡ ys
{-# ATP prove ≈→≡ #-}

postulate ≉→≢ : ∀ {xs ys} → xs ≉ ys → xs ≢ ys
{-# ATP prove ≉→≢ #-}
