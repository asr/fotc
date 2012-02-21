------------------------------------------------------------------------------
-- Predicate logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module contains some examples showing the use of the ATPs to
-- prove theorems from predicate logic.

module PredicateLogic.TheoremsATP where

open import PredicateLogic.Base

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰    : Set
  P¹ Q¹ : D → Set
  P²    : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
{-
      φ(x)
  -----------  ∀-intro
    ∀x.φ(x)

    ∀x.φ(x)
  -----------  ∀-elim
     φ(t)

      φ(t)
  -----------  ∃-intro
    ∃x.φ(x)

   ∃x.φ(x)   φ(x) → ψ
 ----------------------  ∃-elim
           ψ
-}

postulate
  ∀-intro : ((x : D) → P¹ x) → ⋀ P¹
  ∀-elim  : ⋀ P¹ → (t : D) → P¹ t
  -- It is necessary to assume a non-empty domain. See
  -- PredicateLogic.NonEmptyDomain.TheoremsI/ATP.∃I.
  ∃-intro : ((t : D) → P¹ t) → ∃ P¹
  ∃-elim'  : ∃ P¹ → ((x : D) → P¹ x → P⁰) → P⁰
{-# ATP prove ∀-intro #-}
{-# ATP prove ∀-elim #-}
{-# ATP prove ∃-intro #-}
{-# ATP prove ∃-elim' #-}

-- Generalization of De Morgan's laws.
postulate
  gDM₁ : ¬ (⋀ P¹) ↔ (∃[ x ] ¬ (P¹ x))
  gDM₂ : ¬ (∃ P¹) ↔ ⋀ (λ x → ¬ (P¹ x))
  gDM₃ : ⋀ P¹     ↔ ¬ (∃[ x ] ¬ (P¹ x))
  gDM₄ : ∃ P¹     ↔ ¬ (⋀ (λ x → ¬ (P¹ x)))
{-# ATP prove gDM₁ #-}
{-# ATP prove gDM₂ #-}
{-# ATP prove gDM₃ #-}
{-# ATP prove gDM₄ #-}

-- The order of quantifiers of the same sort is irrelevant.
postulate
  ∀-ord : ⋀ (λ x → ⋀ (λ y → P² x y)) ↔ ⋀ (λ y → ⋀ (λ x → P² x y))
  ∃-ord : (∃[ x ] ∃[ y ] P² x y) ↔ (∃[ y ] ∃[ x ] P² x y)
{-# ATP prove ∀-ord #-}
{-# ATP prove ∃-ord #-}

-- Quantification over a variable that does not occur can be delete.
postulate
  ∀-erase : ⋀ (λ _ → P⁰) ↔ P⁰
  ∃-erase : (∃[ x ] P⁰ ∧ P¹ x) ↔ P⁰ ∧ (∃[ x ] P¹ x)
{-# ATP prove ∀-erase #-}
{-# ATP prove ∃-erase #-}

-- Distributes laws for the quantifiers.
postulate
  ∀-dist : ⋀ (λ x → P¹ x ∧ Q¹ x) ↔ (⋀ P¹ ∧ ⋀ Q¹)
  ∃-dist : (∃[ x ] P¹ x ∨ Q¹ x) ↔ (∃ P¹ ∨ ∃ Q¹)
{-# ATP prove ∀-dist #-}
{-# ATP prove ∃-dist #-}

-- Interchange of quantifiers.
-- The related theorem ∀x∃y.Pxy → ∃y∀x.Pxy is not (classically) valid.
postulate ∃∀ : ∃[ x ] (⋀ λ y → P² x y) → ⋀ λ y → ∃[ x ] P² x y
{-# ATP prove ∃∀ #-}
