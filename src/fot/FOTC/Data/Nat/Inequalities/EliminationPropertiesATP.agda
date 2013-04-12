------------------------------------------------------------------------------
-- Elimination properties for the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities.EliminationPropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------

0<0→⊥ : ¬ (zero < zero)
0<0→⊥ 0<0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}

x<0→⊥ : ∀ {n} → N n → ¬ (n < zero)
x<0→⊥ nzero 0<0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
x<0→⊥ (nsucc Nn) Sn<0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}

x<x→⊥ : ∀ {n} → N n → ¬ (n < n)
x<x→⊥ nzero 0<0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
x<x→⊥ (nsucc {n} Nn) Sn<Sn = prf (x<x→⊥ Nn)
  where postulate prf : ¬ (n < n) → ⊥
        {-# ATP prove prf #-}

0>x→⊥ : ∀ {n} → N n → ¬ (zero > n)
0>x→⊥ nzero 0>0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
0>x→⊥ (nsucc Nn) 0>Sn = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}

S≤0→⊥ : ∀ {n} → N n → ¬ (succ₁ n ≤ zero)
S≤0→⊥ nzero S0≤0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
S≤0→⊥ (nsucc {n} Nn) SSn≤0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}

0≥S→⊥ : ∀ {n} → N n → ¬ (zero ≥ succ₁ n)
0≥S→⊥ Nn 0≥Sn = prf
  where postulate prf : ⊥
        {-# ATP prove prf S≤0→⊥ #-}

x<y→y<x→⊥ : ∀ {m n} → N m → N n → m < n → ¬ (n < m)
x<y→y<x→⊥ nzero Nn 0<n n<0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf 0>x→⊥ #-}
x<y→y<x→⊥ (nsucc Nm) nzero Sm<0 0<Sm = prf
  where postulate prf : ⊥
        {-# ATP prove prf 0>x→⊥ #-}
x<y→y<x→⊥ (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn Sn<Sm =
  prf₁ (x<y→y<x→⊥ Nm Nn prf₂)
  where postulate prf₁ : ¬ (n < m) → ⊥
        {-# ATP prove prf₁ #-}

        postulate prf₂ : lt m n ≡ true
        {-# ATP prove prf₂ #-}

postulate S≯0→⊥ : ∀ {n} → ¬ (succ₁ n ≯ zero)
{-# ATP prove S≯0→⊥ #-}
