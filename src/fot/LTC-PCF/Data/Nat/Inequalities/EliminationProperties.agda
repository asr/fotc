------------------------------------------------------------------------------
-- Elimation properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities.EliminationProperties where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.ConversionRules

------------------------------------------------------------------------------

0<0→⊥ : ¬ LT zero zero
0<0→⊥ 0<0 = true≢false (trans (sym 0<0) <-00)

S<0→⊥ : ∀ {n}  → ¬ LT (succ₁ n) zero
S<0→⊥ {n} h = true≢false (trans (sym h) (<-S0 n))

x<0→⊥ : ∀ {n} → N n → ¬ (LT n zero)
x<0→⊥ nzero     0<0  = 0<0→⊥ 0<0
x<0→⊥ (nsucc _) Sn<0 = S<0→⊥ Sn<0

x<x→⊥ : ∀ {n} → N n → ¬ (LT n n)
x<x→⊥ nzero          0<0   = 0<0→⊥ 0<0
x<x→⊥ (nsucc {n} Nn) Sn<Sn = ⊥-elim (x<x→⊥ Nn (trans (sym (<-SS n n)) Sn<Sn))

0>0→⊥ : ¬ GT zero zero
0>0→⊥ 0>0 = true≢false (trans (sym 0>0) <-00)

0>S→⊥ : ∀ {n} → ¬ GT zero (succ₁ n)
0>S→⊥ {n} h = true≢false (trans (sym h) (<-S0 n))

0>x→⊥ : ∀ {n} → N n → ¬ (GT zero n)
0>x→⊥ nzero     0>0  = 0>0→⊥ 0>0
0>x→⊥ (nsucc _) 0>Sn = 0>S→⊥ 0>Sn

x>x→⊥ : ∀ {n} → N n → ¬ (GT n n)
x>x→⊥ Nn = x<x→⊥ Nn

S≤0→⊥ : ∀ {n} → N n → ¬ (LE (succ₁ n) zero)
S≤0→⊥ nzero S0≤0 =
  true≢false (trans (sym S0≤0) (trans (<-SS zero zero) <-00))
S≤0→⊥ (nsucc {n} _) SSn≤0 =
  true≢false (trans (sym SSn≤0) (trans (<-SS (succ₁ n) zero) (<-S0 n)))

0≥S→⊥ : ∀ {n} → N n → ¬ (GE zero (succ₁ n))
0≥S→⊥ Nn 0≥Sn = S≤0→⊥ Nn 0≥Sn

x<y→y<x→⊥ : ∀ {m n} → N m → N n → LT m n → ¬ (LT n m)
x<y→y<x→⊥ nzero          Nn             0<n   n<0   = ⊥-elim (0>x→⊥ Nn n<0)
x<y→y<x→⊥ (nsucc Nm)     nzero          Sm<0  0<Sm  = ⊥-elim (0>x→⊥ (nsucc Nm) Sm<0)
x<y→y<x→⊥ (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn Sn<Sm =
  x<y→y<x→⊥ Nm Nn (trans (sym (<-SS m n)) Sm<Sn) (trans (sym (<-SS n m)) Sn<Sm)

S≯0→⊥ : ∀ {n} → ¬ (NGT (succ₁ n) zero)
S≯0→⊥ {n} h = ⊥-elim (true≢false (trans (sym (<-0S n)) h))
