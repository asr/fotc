{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

From: Hancock (2008). (Ordinal-theoretic) proof theory.

module Ordinals where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Ω : Set where
  zero : Ω
  succ : Ω → Ω
  limN : (ℕ → Ω) → Ω

inj : ℕ → Ω
inj zero     = zero
inj (succ n) = succ (inj n)

ω : Ω
ω = limN (λ n → inj n)

ω+1 : Ω
ω+1 = succ ω

data Ω₂ : Set where
  zero : Ω₂
  succ : Ω₂ → Ω₂
  limN : (ℕ → Ω₂) → Ω₂
  limΩ : (Ω → Ω₂) → Ω₂

inj₁ : Ω → Ω₂
inj₁ zero     = zero
inj₁ (succ o) = succ (inj₁ o)
inj₁ (limN f) = limN (λ n → inj₁ (f n))

ω₁ : Ω₂
ω₁ = limΩ (λ o → inj₁ o)
