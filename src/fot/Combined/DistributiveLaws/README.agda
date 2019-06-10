------------------------------------------------------------------------------
-- Distributive laws on a binary operation (Stanovský example)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.README where

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
open import Combined.DistributiveLaws.Base

-- The combined proofs
open import Combined.DistributiveLaws.Lemma3
open import Combined.DistributiveLaws.Lemma4
open import Combined.DistributiveLaws.Lemma5
open import Combined.DistributiveLaws.Lemma6
open import Combined.DistributiveLaws.TaskB-AllSteps
open import Combined.DistributiveLaws.TaskB-HalvedSteps
open import Combined.DistributiveLaws.TaskB-TopDown

-- Unproven theorem by the ATPs
open import Combined.DistributiveLaws.TaskB.Unproved

------------------------------------------------------------------------------
-- References:
--
-- Stanovský, David (2008). Distributive Groupoids are
-- Symmetrical-by-Medial: An Elementary Proof. Commentations
-- Mathematicae Universitatis Carolinae 49.4, pp. 541–546.
