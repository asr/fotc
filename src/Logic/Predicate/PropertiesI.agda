------------------------------------------------------------------------------
-- Predicate logic examples
------------------------------------------------------------------------------

module Logic.Predicate.PropertiesI where

open import Logic.Constants

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
∃I : ((t : D) → P¹ t) → ∃ P¹
∃I ∀p¹ = D≠∅ , ∀p¹ D≠∅

∃E : ∃ P¹ → ((x : D) → P¹ x → P⁰) → P⁰
∃E (x , p¹x) f = f x p¹x

-- Generalization of De Morgan's laws.
gDM₂ : ¬ (∃ P¹) ↔ ((x : D) → ¬ (P¹ x))
gDM₂ = l→r , r→l
  where
    l→r : ¬ (∃ P¹) → (x : D) → ¬ (P¹ x)
    l→r ∃p¹→⊥ x ∀p¹ = ∃p¹→⊥ (x , ∀p¹)

    r→l : ((x : D) → ¬ (P¹ x)) → ¬ (∃ P¹)
    r→l ∀¬p¹ ∃p¹ = ∀¬p¹ (∃-proj₁ ∃p¹) (∃-proj₂ ∃p¹)

-- Quantification over a variable that does not occur can be delete.
∃-erase₁ : ∃ (λ _ → P⁰) ↔ P⁰
∃-erase₁ = l→r , r→l
  where
    l→r : ∃ (λ _ → P⁰) → P⁰
    l→r (_ , p0) = p0

    r→l : P⁰ → ∃ (λ _ → P⁰)
    r→l p0 = D≠∅ , p0

∃-erase₂ : ∃ (λ x → P⁰ ∧ P¹ x) ↔ P⁰ ∧ ∃ (λ x → P¹ x)
∃-erase₂ = l→r , r→l
  where
    l→r : ∃ (λ x → P⁰ ∧ P¹ x) → P⁰ ∧ ∃ (λ x → P¹ x)
    l→r (x , p0 , p¹x) = p0 , x , p¹x

    r→l : P⁰ ∧ ∃ (λ x → P¹ x) → ∃ (λ x → P⁰ ∧ P¹ x)
    r→l (p0 , x , p¹x) = x , p0 , p¹x

∃-erase₃ : ∃ (λ x → P⁰ ∨ P¹ x) ↔ P⁰ ∨ ∃ (λ x → P¹ x)
∃-erase₃ = l→r , r→l
  where
    l→r : ∃ (λ x → P⁰ ∨ P¹ x) → P⁰ ∨ ∃ (λ x → P¹ x)
    l→r (x , inj₁ p0)  = inj₁ p0
    l→r (x , inj₂ p¹x) = inj₂ (x , p¹x)

    r→l : P⁰ ∨ ∃ (λ x → P¹ x) → ∃ (λ x → P⁰ ∨ P¹ x)
    r→l (inj₁ p0)        = D≠∅ , (inj₁ p0)
    r→l (inj₂ (x , p¹x)) = x , inj₂ p¹x
