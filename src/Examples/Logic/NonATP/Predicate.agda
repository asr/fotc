------------------------------------------------------------------------------
-- Predicate logic examples
------------------------------------------------------------------------------

module Examples.Logic.NonATP.Predicate where

open import Examples.Logic.Constants

------------------------------------------------------------------------------
-- We postulate some predicate symbols.
postulate
  P⁰ : Set
  P¹ : D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
{-
        φ(x)          ∀x.φ(x)          φ(t)           ∃x.φ(x)   φ(x) → ψ
  ∀I ---------    ∀E ---------    ∃I ---------    ∃E --------------------
      ∀x.φ(x)          φ(t)           ∃x.φ(x)               ψ
-}

-- It is necessary postulate a non-empty domain.
∃DI : ((t : D) → P¹ t) → ∃D P¹
∃DI ∀p¹ = D≠∅ , ∀p¹ D≠∅

∃DE : ∃D P¹ → ((x : D) → P¹ x → P⁰) → P⁰
∃DE (x , p¹x) f = f x p¹x

-- Generalization of De Morgan's laws.
gDM₂ : ¬ (∃D P¹) ↔ ((x : D) → ¬ (P¹ x))
gDM₂ = l→r , r→l
  where
    l→r : ¬ (∃D P¹) → (x : D) → ¬ (P¹ x)
    l→r ∃p¹→⊥ x ∀p¹ = ∃p¹→⊥ (x , ∀p¹)

    r→l : ((x : D) → ¬ (P¹ x)) → ¬ (∃D P¹)
    r→l ∀¬p¹ ∃p¹ = ∀¬p¹ (∃D-proj₁ ∃p¹) (∃D-proj₂ ∃p¹)

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
