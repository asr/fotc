-- Tested with the development version of Agda on 11 June 2012.

module InductionPrinciples where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

-- The induction principle without the hypothesis N n in the inductive step.
ind₁ : Set₁
ind₁ = (P : D → Set) →
       P zero →
       (∀ {n} → P n → P (succ n)) →
       ∀ {n} → N n → P n

-- The induction principle with the hypothesis N n in the inductive step.
ind₂ : Set₁
ind₂ = (P : D → Set) →
       P zero →
       (∀ {n} → N n → P n → P (succ n)) →
       ∀ {n} → N n → P n

-- We couldn't prove ind₂ from ind₁
1→2 : ind₁ → ind₂
1→2 h P P0 is {n} Nn = {!!}
