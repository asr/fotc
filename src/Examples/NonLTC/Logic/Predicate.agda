------------------------------------------------------------------------------
-- Predicate logic examples
------------------------------------------------------------------------------

module Examples.NonLTC.Logic.Predicate where

open import Examples.NonLTC.Logic.Constants

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

-- The introduction and elimination rules for the quantifiers are theorems.

-- It is necessary postulate a non-empty domain.
∃DI : ((t : D) → P¹ t) → ∃D P¹
∃DI f = D≠∅ , f D≠∅

-- Quantification over a variable that does not occur can be delete.
∃-erase₁ : ∃D (λ _ → P⁰) ↔ P⁰
∃-erase₁ = l→r , r→l
  where
    l→r : ∃D (λ _ → P⁰) → P⁰
    l→r (_ , p0) = p0

    r→l : P⁰ → ∃D (λ _ → P⁰)
    r→l p0 = D≠∅ , p0

∃-erase₂ : ∃D (λ x → P⁰ ∧ P¹ x) ↔ P⁰ ∧ ∃D (λ x → P¹ x)
∃-erase₂ = l→r , r→l
  where
    l→r : ∃D (λ x → P⁰ ∧ P¹ x) → P⁰ ∧ ∃D (λ x → P¹ x)
    l→r (x , p0 , p¹x) = p0 , x , p¹x

    r→l : P⁰ ∧ ∃D (λ x → P¹ x) → ∃D (λ x → P⁰ ∧ P¹ x)
    r→l (p0 , x , p¹x) = x , p0 , p¹x

∃-erase₃ : ∃D (λ x → P⁰ ∨ P¹ x) ↔ P⁰ ∨ ∃D (λ x → P¹ x)
∃-erase₃ = l→r , r→l
  where
    l→r : ∃D (λ x → P⁰ ∨ P¹ x) → P⁰ ∨ ∃D (λ x → P¹ x)
    l→r (x , inj₁ p0)  = inj₁ p0
    l→r (x , inj₂ p¹x) = inj₂ (x , p¹x)

    r→l : P⁰ ∨ ∃D (λ x → P¹ x) → ∃D (λ x → P⁰ ∨ P¹ x)
    r→l (inj₁ p0)        = D≠∅ , (inj₁ p0)
    r→l (inj₂ (x , p¹x)) = x , inj₂ p¹x
