{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.PA.Inductive.CanonicalTerm where

-- We cannot extract a canonical term from a non-intuitionistic proof.

open import PA.Inductive.Base
open import PA.Inductive.PropertiesI

------------------------------------------------------------------------------
-- The existential projections

∃-proj₁ : ∀ {A} → ∃ A → M
∃-proj₁ (x , _) = x

∃-proj₂ : ∀ {A} → (h : ∃ A) → A (∃-proj₁ h)
∃-proj₂ (_ , Ax) = Ax

------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A

-- The principle of indirect proof (proof by contradiction).
¬-elim : ∀ {A} → (¬ A → ⊥) → A
¬-elim h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

-- ∃ in terms of ∀ and ¬.
¬∃¬→∀ : {A : M → Set} → ¬ (∃[ x ] ¬ A x) → ∀ {x} → A x
¬∃¬→∀ h {x} = ¬-elim (λ h₁ → h (x , h₁))

------------------------------------------------------------------------------

-- Intuitionistic proof.
proof₁ : ∃[ x ] x ≢ succ x
proof₁ = succ zero , x≢Sx

-- Non-intuitionistic proof.
proof₂ : ∃[ x ] x ≢ succ x
proof₂ = ¬-elim (λ h → x≢Sx {succ zero} (¬∃¬→∀ h))

-- We can extract a canonical term from an intuitionistic proof.
canonicalTerm₁ : ∃-proj₁ proof₁ ≡ succ zero
canonicalTerm₁ = refl

-- We cannot extract a canonical term from a non-intuitionistic proof.
-- canonicalTerm₂ : ∃-proj₁ proof₂ ≡ succ zero
-- canonicalTerm₂ = {!refl!}

-- Agda error:
--
-- ∃-proj₁ ([ (λ a → a) , (λ ¬a → ⊥-elim (x≢Sx (¬∃¬→∀ ¬a))) ] pem) !=
-- succ zero of type M
-- when checking that the expression refl has type
-- ∃-proj₁ proof₂ ≡ succ zero
