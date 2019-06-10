------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-pattern-matching      #-}
{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}

module InteractiveFOT.PA.Axiomatic.Standard.NoPatternMatchingOnRefl where

open import Interactive.PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------
-- From Interactive.PA.Axiomatic.Standard.Properties

-- Congruence properties

succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succCong {m} h = subst (λ t → succ m ≡ succ t) h refl

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong {m} {o = o} h = subst (λ t → m + o ≡ t + o) h refl

+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong {m} {n} h = subst (λ t → m + n ≡ m + t) h refl
