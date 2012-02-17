------------------------------------------------------------------------------
-- Predicate logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PredicateLogic.TheoremsI where

open import PredicateLogic.Constants

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set
  P² : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
{-
        φ(x)          ∀x.φ(x)          φ(t)           ∃x.φ(x)   φ(x) → ψ
  ∀I ---------    ∀E ---------    ∃I ---------    ∃E --------------------
      ∀x.φ(x)          φ(t)           ∃x.φ(x)               ψ
-}

-- It is necessary postulate a non-empty domain. See
-- PredicateLogic.NonEmptyDomain.TheoremsI/ATP.∃I.
-- ∃I : ((t : D) → P¹ t) → ∃ P¹

∃E : ∃ P¹ → ((x : D) → P¹ x → P⁰) → P⁰
∃E h₁ h₂ = ∃-elim h₁ h₂

-- Generalization of De Morgan's laws.
gDM₂ : ¬ (∃ P¹) ↔ ((x : D) → ¬ (P¹ x))
gDM₂ = l→r , r→l
  where
  l→r : ¬ (∃ P¹) → (x : D) → ¬ (P¹ x)
  l→r h x p¹ = h (x , p¹)

  r→l : ((x : D) → ¬ (P¹ x)) → ¬ (∃ P¹)
  r→l h₁ h₂ = ∃-elim h₂ h₁

-- Quantification over a variable that does not occur can be delete.
∃-erase : (∃[ x ] P⁰ ∧ P¹ x) ↔ P⁰ ∧ (∃[ x ] P¹ x)
∃-erase = l→r , r→l
  where
  l→r : ∃[ x ] P⁰ ∧ P¹ x → P⁰ ∧ (∃[ x ] P¹ x)
  l→r h = ∃-elim h (λ x prf → (∧-proj₁ prf) , (x , (∧-proj₂ prf)))

  r→l : P⁰ ∧ (∃[ x ] P¹ x) → ∃[ x ] P⁰ ∧ P¹ x
  r→l (p⁰ , h) = ∃-elim h (λ x prf → x , p⁰ , prf)

-- Interchange of quantifiers.
-- The related theorem ∀x∃y.Pxy → ∃y∀x.Pxy is not (classically) valid.
∃∀ : ∃[ x ] (⋀ λ y → P² x y) → ⋀ λ y → ∃[ x ] P² x y
∃∀ h y = ∃-elim h (λ x prf → x , (prf y))
