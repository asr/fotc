------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Using the ATPs we don't have to postulate a non-empty domain because
-- the ATPs assume it.

module PredicateLogic.NonEmptyDomain.TheoremsATP where

open import PredicateLogic.Base

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

postulate ∃-intro : ((t : D) → P¹ t) → ∃ P¹
{-# ATP prove ∃-intro #-}

-- Quantification over a variable that does not occur can be delete.
postulate
  ∃-erase₁ : ∃ (λ _ → P⁰) ↔ P⁰
  ∃-erase₂ : (∃[ x ] P⁰ ∨ P¹ x) ↔ P⁰ ∨ (∃[ x ] P¹ x)
{-# ATP prove ∃-erase₁ #-}
{-# ATP prove ∃-erase₂ #-}
