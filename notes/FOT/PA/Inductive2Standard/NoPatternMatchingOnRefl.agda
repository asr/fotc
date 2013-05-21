------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.PA.Inductive2Standard.NoPatternMatchingOnRefl where

open import PA.Inductive.Base

------------------------------------------------------------------------------
-- From PA.Inductive2Standard

-- 20 May 2013. Requires the predecessor function.
-- PA₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
