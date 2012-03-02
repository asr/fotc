------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Using the ATPs we don't have to use the postulate about a non-empty
-- domain because the ATPs assume it.

module PredicateLogic.NonEmptyDomain.TheoremsATP where

open import PredicateLogic.Base

-- References:
-- Elliott Mendelson. Introduction to mathematical logic. Chapman &
-- Hall, 4th edition, 1997.

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

-- TODO: 2012-02-28. Fix the existential introduction rule.
-- ∃-intro : ((t : D) → P¹ t) → ∃ P¹
-- {-# ATP prove ∃-intro #-}

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson, 1997, proposition 2.18 (b), p. 70).
postulate
  ∃-erase-add₁ : ∃ (λ _ → P⁰) ↔ P⁰
{-# ATP prove ∃-erase-add₁ #-}

-- Quantification over a variable that does not occur can be erased or
-- added.
postulate
  ∃-erase-add₂ : (∃[ x ] P⁰ ∨ P¹ x) ↔ P⁰ ∨ (∃[ x ] P¹ x)
{-# ATP prove ∃-erase-add₂ #-}
