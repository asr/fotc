------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

module PredicateLogic.NonEmptyDomain.TheoremsI where

open import PredicateLogic.Constants
open import PredicateLogic.NonEmptyDomain

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

∃I : ((t : D) → P¹ t) → ∃ P¹
∃I ∀p¹ = D≠∅ , ∀p¹ D≠∅

-- Quantification over a variable that does not occur can be delete.
∃-erase₁ : ∃ (λ _ → P⁰) ↔ P⁰
∃-erase₁ = l→r , r→l
  where
    l→r : ∃ (λ _ → P⁰) → P⁰
    l→r (_ , p0) = p0

    r→l : P⁰ → ∃ (λ _ → P⁰)
    r→l p0 = D≠∅ , p0

∃-erase₂ : ∃ (λ x → P⁰ ∨ P¹ x) ↔ P⁰ ∨ ∃ (λ x → P¹ x)
∃-erase₂ = l→r , r→l
  where
    l→r : ∃ (λ x → P⁰ ∨ P¹ x) → P⁰ ∨ ∃ (λ x → P¹ x)
    l→r (x , inj₁ p0)  = inj₁ p0
    l→r (x , inj₂ p¹x) = inj₂ (x , p¹x)

    r→l : P⁰ ∨ ∃ (λ x → P¹ x) → ∃ (λ x → P⁰ ∨ P¹ x)
    r→l (inj₁ p0)        = D≠∅ , (inj₁ p0)
    r→l (inj₂ (x , p¹x)) = x , inj₂ p¹x
