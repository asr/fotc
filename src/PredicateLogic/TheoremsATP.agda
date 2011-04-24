------------------------------------------------------------------------------
-- Predicate logic theorems
------------------------------------------------------------------------------

-- This module contains some examples showing the use of the ATPs to
-- prove theorems from predicate logic.

module PredicateLogic.TheoremsATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰    : Set
  P¹ Q¹ : D → Set
  P²    : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
{-
        φ(x)          ∀x.φ(x)          φ(t)           ∃x.φ(x)   φ(x) → ψ
  ∀I ---------    ∀E ---------    ∃I ---------    ∃E --------------------
      ∀x.φ(x)          φ(t)           ∃x.φ(x)               ψ
-}

postulate
  ∀I : ((x : D) → P¹ x) → ⋀ P¹
  ∀E : ⋀ P¹ → (t : D) → P¹ t
  -- It is necessary postulate a non-empty domain. See
  -- PredicateLogic.NonEmptyDomain.TheoremsATP.∃I.
  ∃I : ((t : D) → P¹ t) → ∃ P¹
  ∃E : ∃ P¹ → ((x : D) → P¹ x → P⁰) → P⁰
{-# ATP prove ∀I #-}
{-# ATP prove ∀E #-}
{-# ATP prove ∃E #-}

-- Generalization of De Morgan's laws.
postulate
  gDM₁ : ¬ (⋀ P¹) ↔ ∃ (λ x → ¬ (P¹ x))
  gDM₂ : ¬ (∃ P¹) ↔ ⋀ (λ x → ¬ (P¹ x))
  gDM₃ : ⋀ P¹     ↔ ¬ (∃ (λ x → ¬ (P¹ x)))
  gDM₄ : ∃ P¹     ↔ ¬ (⋀ (λ x → ¬ (P¹ x)))
{-# ATP prove gDM₁ #-}
{-# ATP prove gDM₂ #-}
{-# ATP prove gDM₃ #-}
{-# ATP prove gDM₄ #-}

-- The order of quantifiers of the same sort is irrelevant.
postulate
  ∀-ord : ⋀ (λ x → ⋀ (λ y → P² x y)) ↔ ⋀ (λ y → ⋀ (λ x → P² x y))
  ∃-ord : ∃ (λ x → ∃ (λ y → P² x y)) ↔ ∃ (λ y → ∃ (λ x → P² x y))
{-# ATP prove ∀-ord #-}
{-# ATP prove ∃-ord #-}

-- Quantification over a variable that does not occur can be delete.
postulate
  ∀-erase : ⋀ (λ _ → P⁰) ↔ P⁰
  ∃-erase : ∃ (λ x → P⁰ ∧ P¹ x) ↔ P⁰ ∧ ∃ (λ x → P¹ x)
{-# ATP prove ∀-erase #-}
{-# ATP prove ∃-erase #-}

-- Distributes laws for the quantifiers.
postulate
  ∀-dist : ⋀ (λ x → P¹ x ∧ Q¹ x) ↔ (⋀ P¹ ∧ ⋀ Q¹)
  ∃-dist : ∃ (λ x → P¹ x ∨ Q¹ x) ↔ (∃ P¹ ∨ ∃ Q¹)
{-# ATP prove ∀-dist #-}
{-# ATP prove ∃-dist #-}
