------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-pattern-matching      #-}
{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}

module InteractiveFOT.PA.Inductive2Mendelson.NoPatternMatchingOnRefl where

open import Interactive.PA.Inductive.Base

------------------------------------------------------------------------------
-- From Interactive.PA.Inductive2Mendelson

S₁ :  ∀ {m n o} → m ≡ n → m ≡ o → n ≡ o
S₁ h₁ h₂ = trans (sym h₁) h₂

S₂ : ∀ {m n} → m ≡ n → succ m ≡ succ n
S₂ {m} h = subst (λ t → succ m ≡ succ t) h refl

-- 20 May 2013. Requires the predecessor function.
-- S₄ : ∀ {m n} → succ m ≡ succ n → m ≡ n
