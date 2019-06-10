------------------------------------------------------------------------------
-- Distributive laws on a binary operation (Stanovský example)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.DistributiveLaws.README where

------------------------------------------------------------------------------
-- Description

-- Let _·_ be a left-associative binary operation which satifies the
-- left and right distributive axioms:
--
-- ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
-- ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z).

-- We prove some properties of Stanovský (2008): Task B, Lemma 3,
-- Lemma 4, Lemma 5 (Task A) and Lemma 6.

------------------------------------------------------------------------------
-- The axioms
open import Interactive.DistributiveLaws.Base

-- The interactive proofs
open import Interactive.DistributiveLaws.TaskB

------------------------------------------------------------------------------
-- References:
--
-- Stanovský, David (2008). Distributive Groupoids are
-- Symmetrical-by-Medial: An Elementary Proof. Commentations
-- Mathematicae Universitatis Carolinae 49.4, pp. 541–546.
