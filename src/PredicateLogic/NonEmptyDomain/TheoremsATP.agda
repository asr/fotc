------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

-- Using the ATPs we don't have to postulate a non-empty domain because
-- the ATPs assume it.

module PredicateLogic.NonEmptyDomain.TheoremsATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

postulate ∃I : ((t : D) → P¹ t) → ∃ P¹
{-# ATP prove ∃I #-}

-- Quantification over a variable that does not occur can be delete.
postulate
  ∃-erase₁ : ∃ (λ _ → P⁰) ↔ P⁰
  ∃-erase₂ : ∃ (λ x → P⁰ ∨ P¹ x) ↔ P⁰ ∨ ∃ (λ x → P¹ x)
{-# ATP prove ∃-erase₁ #-}
{-# ATP prove ∃-erase₂ #-}
