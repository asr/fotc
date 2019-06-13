------------------------------------------------------------------------------
-- From Mendelson's axioms to standard axioms
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From Mendelson's axioms we can prove the standard axioms.

module Interactive.PA.Mendelson2Standard where

open import Interactive.PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------

PA₁ : ∀ {n} → zero ≉ succ n
PA₁ = S₃

PA₂ : ∀ {m n} → succ m ≈ succ n → m ≈ n
PA₂ = S₄

PA₃ : ∀ n → zero + n ≈ n
PA₃ = S₅

PA₄ : ∀ m n → succ m + n ≈ succ (m + n)
PA₄ = S₆

PA₅ : ∀ n → zero * n ≈ zero
PA₅ = S₇

PA₆ : ∀ m n → succ m * n ≈ n + m * n
PA₆ = S₈

ℕ-ind : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
ℕ-ind = S₉
