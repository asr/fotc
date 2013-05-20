------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.PA.Inductive2Standard.NoPatternMatchingOnRefl where

open import PA.Inductive.Base

------------------------------------------------------------------------------
-- From PA.Inductive2Standard

-- TODO: 20 May 2013.
-- PA₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
