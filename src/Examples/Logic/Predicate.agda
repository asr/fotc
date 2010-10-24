------------------------------------------------------------------------------
-- Predicate logic examples
------------------------------------------------------------------------------

-- This module contains some examples showing the use of the ATPs to
-- prove theorems from predicate logic.

module Examples.Logic.Predicate where

open import Examples.Logic.Constants

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰    : Set
  P¹ Q¹ : D → Set
  P²    : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
postulate
  ∀DI : ((x : D) → P¹ x) → ∀D P¹
  ∀DE : ∀D P¹ → (t : D) → P¹ t
  -- This elimination rule cannot prove in Coq because in Coq we can
  -- have empty domains. We do not have this problem because the ATPs
  -- assume a non-empty domain.
  ∃DI : ((t : D) → P¹ t) → ∃D P¹
  -- TODO: ∃E : (x : D) → ∃D P¹ → (P¹ x → Q¹ x) → Q¹ x
{-# ATP prove ∀DI #-}
{-# ATP prove ∀DE #-}
{-# ATP prove ∃DI #-}
-- {-# ATP prove ∃DE #-}

-- Generalization of De Morgan's laws.
postulate
  gDM₁ : ¬ (∀D P¹) ↔ ∃D (λ x → ¬ (P¹ x))
  gDM₂ : ¬ (∃D P¹) ↔ ∀D (λ x  → ¬ (P¹ x))
  gDM₃ : ∀D P¹     ↔ ¬ (∃D (λ x → ¬ (P¹ x)))
  gDM₄ : ∃D P¹     ↔ ¬ (∀D (λ x → ¬ (P¹ x)))
{-# ATP prove gDM₁ #-}
{-# ATP prove gDM₂ #-}
{-# ATP prove gDM₃ #-}
{-# ATP prove gDM₄ #-}

-- The order of quantifiers of the same sort is irrelevant.
postulate
  ord₁ : ∀D (λ x → ∀D (λ y → P² x y)) ↔ ∀D (λ y → ∀D (λ x → P² x y))
  ord₂ : ∃D (λ x → ∃D (λ y → P² x y)) ↔ ∃D (λ y → ∃D (λ x → P² x y))
{-# ATP prove ord₁ #-}
{-# ATP prove ord₂ #-}

-- Quantification over a variable that does not occur can be delete.
postulate
  erase₁ : ∀D (λ _ → P⁰) ↔ P⁰
  erase₂ : ∃D (λ _ → P⁰) ↔ P⁰
{-# ATP prove erase₁ #-}
{-# ATP prove erase₂ #-}

-- Distributes laws for the quantifiers.
postulate
  dist₁ : ∀D (λ x → P¹ x ∧ Q¹ x) ↔ (∀D P¹ ∧ ∀D Q¹)
  dist₂ : ∃D (λ x → P¹ x ∨ Q¹ x) ↔ (∃D P¹ ∨ ∃D Q¹)
{-# ATP prove dist₁ #-}
{-# ATP prove dist₂ #-}
