------------------------------------------------------------------------------
-- Distributive laws on a binary operation (Stanovský example)
------------------------------------------------------------------------------

module DistributiveLaws.README where

-- We prove some properties of Stanovský (2008).  Let _·_ be a
-- left-associative binary operation which satifies the left and right
-- distributive axioms:
--
-- ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
-- ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z).

-- Task A (to prove the Lemma₅)
--
-- ∀ x y → (x · y ) · x ≡ x · (y · x).

-- Task B (to prove Proposition 2)
--
-- ∀ u x y z →
-- (x ∙ y ∙ (z ∙ u)) ∙ ((x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
--   x ∙ z ∙ (y ∙ u).

------------------------------------------------------------------------------
-- The axioms
open import DistributiveLaws.Base

-- The interactive and combined proofs
open import DistributiveLaws.TaskA-ATP
open import DistributiveLaws.TaskB-HalvedStepsATP
open import DistributiveLaws.TaskB-I
open import DistributiveLaws.TaskB-TopDownATP

-- Unproven theorem by the ATPs
open import DistributiveLaws.TaskB.UnprovedATP

------------------------------------------------------------------------------
-- References:
--
-- Stanovský, David (2008). Distributive Groupoids are
-- Symmetrical-by-Medial: An Elementary Proof. Commentations
-- Mathematicae Universitatis Carolinae 49.4, pp. 541–546.
