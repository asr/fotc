-- Tested with FOT on 23 April 2012.

module Draft.PA.Inductive.Witness where

-- We cannot extract an existential witness from a non-constructive
-- proof.

open import PA.Inductive.Base
open import PA.Inductive.Properties

------------------------------------------------------------------------------
-- The existential quantifier type on M

-- We add 3 to the fixities of the standard library.
infixr 7 _,_

data ∃ (A : M → Set) : Set where
  _,_ : (x : M) → A x → ∃ A

-- Sugar syntax for the existential quantifier.
syntax ∃ (λ x → e) = ∃[ x ] e

∃-proj₁ : ∀ {A} → ∃ A → M
∃-proj₁ (x , _) = x

∃-proj₂ : ∀ {A} → (h : ∃ A) → A (∃-proj₁ h)
∃-proj₂ (_ , Ax) = Ax

------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems

postulate
  -- The principle of indirect proof (proof by contradiction).
  ¬-elim : ∀ {A} → (¬ A → ⊥) → A

  -- ∃ in terms of ∀ and ¬.
  ¬∃¬→∀ : {A : M → Set} → ¬ (∃[ x ] ¬ A x) → ∀ {x} → A x

------------------------------------------------------------------------------

-- Constructive proof.
proof₁ : ∃[ x ] ¬ (x ≡ succ x)
proof₁ = succ zero , x≢Sx

-- Non-constructive proof.
proof₂ : ∃[ x ] ¬ (x ≡ succ x)
proof₂ = ¬-elim (λ h → x≢Sx {succ zero} (¬∃¬→∀ h))

-- We can extract an existential witness from a constructive proof.
witness₁ : ∃-proj₁ proof₁ ≡ succ zero
witness₁ = refl

-- We cannot extract an existential witness from a non-constructive
-- proof.
-- witness₂ : ∃-proj₁ proof₂ ≡ succ zero
-- witness₂ = {!refl!}

-- Agda error:
--
-- ∃-proj₁ (¬-elim (λ h → x≢Sx (¬∃¬→∀ h))) != succ zero of type M
-- when checking that the expression refl has type
-- ∃-proj₁ proof₂ ≡ succ zero
