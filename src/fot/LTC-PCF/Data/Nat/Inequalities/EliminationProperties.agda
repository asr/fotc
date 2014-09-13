------------------------------------------------------------------------------
-- Elimation properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat.Inequalities.EliminationProperties where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.ConversionRules

------------------------------------------------------------------------------

0<0→⊥ : ¬ (zero < zero)
0<0→⊥ 0<0 = t≢f (trans (sym 0<0) lt-00)

S<0→⊥ : ∀ {n}  → ¬ (succ₁ n < zero)
S<0→⊥ {n} h = t≢f (trans (sym h) (lt-S0 n))

x<0→⊥ : ∀ {n} → N n → ¬ (n < zero)
x<0→⊥ nzero     0<0  = 0<0→⊥ 0<0
x<0→⊥ (nsucc _) Sn<0 = S<0→⊥ Sn<0

x<x→⊥ : ∀ {n} → N n → ¬ (n < n)
x<x→⊥ nzero          0<0   = 0<0→⊥ 0<0
x<x→⊥ (nsucc {n} Nn) Sn<Sn = ⊥-elim (x<x→⊥ Nn (trans (sym (lt-SS n n)) Sn<Sn))

0>0→⊥ : ¬ (zero > zero)
0>0→⊥ 0>0 = t≢f (trans (sym 0>0) lt-00)

0>S→⊥ : ∀ {n} → ¬ (zero > (succ₁ n))
0>S→⊥ {n} h = t≢f (trans (sym h) (lt-S0 n))

0>x→⊥ : ∀ {n} → N n → ¬ (zero > n)
0>x→⊥ nzero     0>0  = 0>0→⊥ 0>0
0>x→⊥ (nsucc _) 0>Sn = 0>S→⊥ 0>Sn

x>x→⊥ : ∀ {n} → N n → ¬ (n > n)
x>x→⊥ Nn = x<x→⊥ Nn

S≤0→⊥ : ∀ {n} → N n → ¬ (succ₁ n ≤ zero)
S≤0→⊥ nzero S0≤0 = t≢f (trans (sym S0≤0) (trans (lt-SS zero zero) lt-00))
S≤0→⊥ (nsucc {n} _) SSn≤0 =
  t≢f (trans (sym SSn≤0) (trans (lt-SS (succ₁ n) zero) (lt-S0 n)))

0≥S→⊥ : ∀ {n} → N n → ¬ (zero ≥ succ₁ n)
0≥S→⊥ Nn 0≥Sn = S≤0→⊥ Nn 0≥Sn

x<y→y<x→⊥ : ∀ {m n} → N m → N n → m < n → ¬ (n < m)
x<y→y<x→⊥ nzero          Nn             0<n   n<0   = ⊥-elim (0>x→⊥ Nn n<0)
x<y→y<x→⊥ (nsucc Nm)     nzero          Sm<0  0<Sm  = ⊥-elim (0>x→⊥ (nsucc Nm) Sm<0)
x<y→y<x→⊥ (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn Sn<Sm =
  x<y→y<x→⊥ Nm Nn (trans (sym (lt-SS m n)) Sm<Sn) (trans (sym (lt-SS n m)) Sn<Sm)

S≯0→⊥ : ∀ {n} → ¬ (succ₁ n ≯ zero)
S≯0→⊥ {n} h = ⊥-elim (t≢f (trans (sym (lt-0S n)) h))
