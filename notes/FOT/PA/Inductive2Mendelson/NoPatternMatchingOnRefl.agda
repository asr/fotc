------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.PA.Inductive2Mendelson.NoPatternMatchingOnRefl where

open import PA.Inductive.Base

------------------------------------------------------------------------------
-- From PA.Inductive2Mendelson

S₁ :  ∀ {m n o} → m ≡ n → m ≡ o → n ≡ o
S₁ h₁ h₂ = trans (sym h₁) h₂

S₂ : ∀ {m n} → m ≡ n → succ m ≡ succ n
S₂ {m} h = subst (λ t → succ m ≡ succ t) h refl

-- TODO: 20 May 2013.
-- S₄ : ∀ {m n} → succ m ≡ succ n → m ≡ n
