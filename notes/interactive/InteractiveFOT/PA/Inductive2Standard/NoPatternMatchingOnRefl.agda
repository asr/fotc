------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-pattern-matching      #-}
{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}

module InteractiveFOT.PA.Inductive2Standard.NoPatternMatchingOnRefl where

open import Interactive.PA.Inductive.Base

------------------------------------------------------------------------------
-- From Interactive.PA.Inductive2Standard

-- 20 May 2013. Requires the predecessor function.
-- PA₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
