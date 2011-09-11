------------------------------------------------------------------------------
-- Predicate logic theorems
------------------------------------------------------------------------------

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

-- It is necessary postulate a non-empty domain.
-- See PredicateLogic.NonEmptyDomainI.
-- ∃I : ((t : D) → P¹ t) → ∃ P¹

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
∃-erase : ∃ (λ x → P⁰ ∧ P¹ x) ↔ P⁰ ∧ ∃ (λ x → P¹ x)
∃-erase = l→r , r→l
  where
  l→r : ∃ (λ x → P⁰ ∧ P¹ x) → P⁰ ∧ ∃ (λ x → P¹ x)
  l→r (x , p0 , p¹x) = p0 , x , p¹x

  r→l : P⁰ ∧ ∃ (λ x → P¹ x) → ∃ (λ x → P⁰ ∧ P¹ x)
  r→l (p0 , x , p¹x) = x , p0 , p¹x

-- Interchange of quantifiers.
-- The related theorem ∀x∃y.Pxy → ∃y∀x.Pxy is not (classically) valid.
∃∀ : ∃ (λ x → ⋀ λ y → P² x y) → ⋀ λ y → ∃ λ x → P² x y
∃∀ (x , h) y = x , h y
