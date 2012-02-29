------------------------------------------------------------------------------
-- Predicate logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PredicateLogic.TheoremsI where

open import PredicateLogic.Base

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set
  P² : D → D → Set

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

-- It is necessary postulate a non-empty domain. See
-- PredicateLogic.NonEmptyDomain.TheoremsI/ATP.∃I.
-- ∃-intro : ((t : D) → P¹ t) → ∃ P¹

∃-elim' : ∃ P¹ → ({x : D} → P¹ x → P⁰) → P⁰
∃-elim' = ∃-elim

-- Generalization of De Morgan's laws.
gDM₂ : ¬ (∃ P¹) ↔ (∀ {x} → ¬ (P¹ x))
gDM₂ = l→r , r→l
  where
  l→r : ¬ (∃ P¹) → ∀ {x} → ¬ (P¹ x)
  l→r h p¹ = h (∃-intro p¹)

  r→l : (∀ {x} → ¬ (P¹ x)) → ¬ (∃ P¹)
  r→l h₁ h₂ = ∃-elim h₂ h₁

-- Quantification over a variable that does not occur can be erased or
-- added.
∃-erase-add : (∃[ x ] P⁰ ∧ P¹ x) ↔ P⁰ ∧ (∃[ x ] P¹ x)
∃-erase-add = l→r , r→l
  where
  l→r : ∃[ x ] P⁰ ∧ P¹ x → P⁰ ∧ (∃[ x ] P¹ x)
  l→r h = ∃-elim h (λ prf → (∧-proj₁ prf) , ∃-intro (∧-proj₂ prf))

  r→l : P⁰ ∧ (∃[ x ] P¹ x) → ∃[ x ] P⁰ ∧ P¹ x
  r→l (p⁰ , h) = ∃-elim h (λ prf → ∃-intro (p⁰ , prf))

-- Interchange of quantifiers.
-- The related theorem ∀x∃y.Pxy → ∃y∀x.Pxy is not (classically) valid.
∃∀ : ∃[ x ] (⋀ λ y → P² x y) → ⋀ λ y → ∃[ x ] P² x y
∃∀ h y = ∃-elim h (λ prf → ∃-intro (prf y))
