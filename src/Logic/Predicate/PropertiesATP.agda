------------------------------------------------------------------------------
-- Predicate logic examples
------------------------------------------------------------------------------

-- This module contains some examples showing the use of the ATPs to
-- prove theorems from predicate logic.

module Logic.Predicate.PropertiesATP where

open import Logic.Constants

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
  -- This elimination rule cannot prove in Agda/Coq because in Agda/Coq we can
  -- have empty domains. We do not have this problem because the ATPs
  -- assume a non-empty domain.
  ∃I : ((t : D) → P¹ t) → ∃ P¹
  ∃E : ∃ P¹ → ((x : D) → P¹ x → P⁰) → P⁰
{-# ATP prove ∀I #-}
{-# ATP prove ∀E #-}
{-# ATP prove ∃I #-}
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
  ∀-erase  : ⋀ (λ _ → P⁰) ↔ P⁰
  ∃-erase₁ : ∃ (λ _ → P⁰) ↔ P⁰
  ∃-erase₂ : ∃ (λ x → P⁰ ∧ P¹ x) ↔ P⁰ ∧ ∃ (λ x → P¹ x)
  ∃-erase₃ : ∃ (λ x → P⁰ ∨ P¹ x) ↔ P⁰ ∨ ∃ (λ x → P¹ x)
{-# ATP prove ∀-erase #-}
{-# ATP prove ∃-erase₁ #-}
{-# ATP prove ∃-erase₂ #-}
{-# ATP prove ∃-erase₃ #-}

-- Distributes laws for the quantifiers.
postulate
  ∀-dist : ⋀ (λ x → P¹ x ∧ Q¹ x) ↔ (⋀ P¹ ∧ ⋀ Q¹)
  ∃-dist : ∃ (λ x → P¹ x ∨ Q¹ x) ↔ (∃ P¹ ∨ ∃ Q¹)
{-# ATP prove ∀-dist #-}
{-# ATP prove ∃-dist #-}
