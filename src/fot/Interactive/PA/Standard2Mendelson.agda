------------------------------------------------------------------------------
-- From standard axioms to Mendelson's axioms
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From the standard axioms we can prove Mendolson's axioms

module Interactive.PA.Standard2Mendelson where

open import Interactive.PA.Axiomatic.Standard.Base
open import Interactive.PA.Axiomatic.Standard.Properties

------------------------------------------------------------------------------

S₁ : ∀ {m n o} → m ≡ n → m ≡ o → n ≡ o
S₁ refl refl = refl

S₂ : ∀ {m n} → m ≡ n → succ m ≡ succ n
S₂ = succCong

S₃ : ∀ {n} → zero ≢ succ n
S₃ = PA₁

S₄ : ∀ {m n} → succ m ≡ succ n → m ≡ n
S₄ = PA₂

S₅ : ∀ n → zero + n ≡ n
S₅ = PA₃

S₆ : ∀ m n → succ m + n ≡ succ (m + n)
S₆ = PA₄

S₇ : ∀ n → zero * n ≡ zero
S₇ = PA₅

S₈ : ∀ m n → succ m * n ≡ n + m * n
S₈ = PA₆

S₉ : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
S₉ = ℕ-ind
