------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PredicateLogic.NonEmptyDomain.TheoremsI where

open import PredicateLogic.Constants
open import PredicateLogic.NonEmptyDomain

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

∃I : ((t : D) → P¹ t) → ∃ P¹
∃I h = D≠∅ , h D≠∅

-- Quantification over a variable that does not occur can be delete.
∃-erase₁ : ∃ (λ _ → P⁰) ↔ P⁰
∃-erase₁ = l→r , r→l
  where
  l→r : ∃ (λ _ → P⁰) → P⁰
  l→r h = ∃-elim h (λ _ prf → prf)

  r→l : P⁰ → ∃ (λ _ → P⁰)
  r→l p⁰ = D≠∅ , p⁰

∃-erase₂ : (∃[ x ] P⁰ ∨ P¹ x) ↔ P⁰ ∨ (∃[ x ] P¹ x)
∃-erase₂ = l→r , r→l
  where
  l→r : ∃[ x ] (P⁰ ∨ P¹ x) → P⁰ ∨ (∃[ x ] P¹ x)
  l→r h = ∃-elim h (λ x prf → [ (λ p⁰ → inj₁ p⁰) , (λ p¹ → inj₂ (x , p¹)) ] prf)

  r→l : P⁰ ∨ (∃[ x ] P¹ x) → ∃[ x ] P⁰ ∨ P¹ x
  r→l (inj₁ p⁰) = D≠∅ , (inj₁ p⁰)
  r→l (inj₂ h)  = ∃-elim h (λ x p¹ → x , (inj₂ p¹))
