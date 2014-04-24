------------------------------------------------------------------------------
-- Distributive laws on a binary operation (Stanovský example)
------------------------------------------------------------------------------

module DistributiveLaws.README where

-- Let _·_ be a left-associative binary operation which satifies the
-- left and right distributive axioms:
--
-- ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
-- ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z).

-- We prove some properties of Stanovský (2008): Proposition 2a,
-- Lemma 3, Lemma 4, Lemma 5 and Lemma 6.

------------------------------------------------------------------------------
-- The axioms
open import DistributiveLaws.Base

-- The interactive and combined proofs
open import DistributiveLaws.Lemma3-ATP
open import DistributiveLaws.Lemma4-ATP
open import DistributiveLaws.Lemma6-ATP
open import DistributiveLaws.Lemma5-ATP
open import DistributiveLaws.Proposition2a-HalvedStepsATP
open import DistributiveLaws.Proposition2a-I
open import DistributiveLaws.Proposition2a-TopDownATP

-- Unproven theorem by the ATPs
open import DistributiveLaws.Proposition2a.UnprovedATP

------------------------------------------------------------------------------
-- References:
--
-- Stanovský, David (2008). Distributive Groupoids are
-- Symmetrical-by-Medial: An Elementary Proof. Commentations
-- Mathematicae Universitatis Carolinae 49.4, pp. 541–546.
