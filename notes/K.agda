{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}  -- No accepted!

module K where

module FOTC where
  postulate D : Set

  data _≡_ (x : D) : D → Set where
    refl : x ≡ x

  K : (x : D)(P : x ≡ x → Set) → P refl → (p : x ≡ x) → P p
  K x P pr refl = pr

module SL where

  open import Data.Nat
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality

  -- Example from: Hofmann and Streicher. The groupoid model refutes
  -- uniqueness of identity proofs.
  thm₁ : ∀ n → n ≡ 0 ⊎ Σ ℕ (λ n' → n ≡ suc n')
  thm₁ zero    = inj₁ refl
  thm₁ (suc n) = inj₂ (n , refl)

  postulate
    indℕ : (P : ℕ → Set) → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n

  thm₂ : ∀ n → n ≡ 0 ⊎ Σ ℕ λ n' → n ≡ suc n'
  thm₂ = indℕ P P0 is
    where
      P : ℕ → Set
      P m = m ≡ 0 ⊎ Σ ℕ λ m' → m ≡ suc m'

      P0 : P 0
      P0 = inj₁ refl

      is : ∀ m → P m → P (suc m)
      is m _ = inj₂ (m , refl)
