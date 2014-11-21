------------------------------------------------------------------------------
-- Existential quantifier on the inductive PA universe
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Inductive.Existential where

------------------------------------------------------------------------------
-- PA universe
open import PA.Inductive.Base.Core

-- The existential quantifier type on M.
data ∃ (A : ℕ → Set) : Set where
  _,_ : (x : ℕ) → A x → ∃ A

-- Sugar syntax for the existential quantifier.
syntax ∃ (λ x → e) = ∃[ x ] e

-- 2012-03-05: We avoid to use the existential elimination or the
-- existential projections because we use pattern matching (and the
-- Agda's with constructor).

-- The existential elimination.
--
-- NB. We do not use the usual type theory elimination with two
-- projections because we are working in first-order logic where we do
-- not need extract a witness from an existence proof.
-- ∃-elim : {A : ℕ → Set}{B : Set} → ∃ A → (∀ {x} → A x → B) → B
-- ∃-elim (_ , Ax) h = h Ax

-- The existential proyections.
-- ∃-proj₁ : ∀ {A} → ∃ A → M
-- ∃-proj₁ (x , _) = x

-- ∃-proj₂ : ∀ {A} → (h : ∃ A) → A (∃-proj₁ h)
-- ∃-proj₂ (_ , Ax) = Ax
