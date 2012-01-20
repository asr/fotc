------------------------------------------------------------------------------
-- Elimation properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities.EliminationProperties where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------

0<0→⊥ : ¬ LT zero zero
0<0→⊥ 0<0 = true≠false $ trans (sym 0<0) <-00

S<0→⊥ : ∀ {d} → ¬ LT (succ₁ d) zero
S<0→⊥ {d} Sd<0 = true≠false $ trans (sym Sd<0) (<-S0 d)

x<0→⊥ : ∀ {n} → N n → ¬ (LT n zero)
x<0→⊥ zN     0<0  = 0<0→⊥ 0<0
x<0→⊥ (sN _) Sn<0 = S<0→⊥ Sn<0

x<x→⊥ : ∀ {n} → N n → ¬ (LT n n)
x<x→⊥ zN          0<0   = 0<0→⊥ 0<0
x<x→⊥ (sN {n} Nn) Sn<Sn = ⊥-elim $ x<x→⊥ Nn (trans (sym $ <-SS n n) Sn<Sn)

0>0→⊥ : ¬ GT zero zero
0>0→⊥ 0>0 = true≠false $ trans (sym 0>0) <-00

0>S→⊥ : ∀ {d} → ¬ GT zero (succ₁ d)
0>S→⊥ {d} 0>Sd = true≠false (trans (sym 0>Sd) (<-S0 d))

0>x→⊥ : ∀ {n} → N n → ¬ (GT zero n)
0>x→⊥ zN     0>0  = 0>0→⊥ 0>0
0>x→⊥ (sN _) 0>Sn = 0>S→⊥ 0>Sn

x>x→⊥ : ∀ {n} → N n → ¬ (GT n n)
x>x→⊥ Nn = x<x→⊥ Nn

S≤0→⊥ : ∀ {n} → N n → ¬ (LE (succ₁ n) zero)
S≤0→⊥ zN         S0≤0  = true≠false (trans (sym S0≤0)
                                           (trans (<-SS zero zero) <-00))
S≤0→⊥ (sN {n} _) SSn≤0 = true≠false (trans (sym SSn≤0)
                                           (trans (<-SS (succ₁ n) zero) (<-S0 n)))

0≥S→⊥ : ∀ {n} → N n → ¬ (GE zero (succ₁ n))
0≥S→⊥ Nn 0≥Sn = S≤0→⊥ Nn 0≥Sn

x<y→y<x→⊥ : ∀ {m n} → N m → N n → LT m n → ¬ (LT n m)
x<y→y<x→⊥ zN      Nn              0<n   n<0   = ⊥-elim (0>x→⊥ Nn n<0)
x<y→y<x→⊥ (sN Nm) zN              Sm<0  0<Sm  = ⊥-elim (0>x→⊥ (sN Nm) Sm<0)
x<y→y<x→⊥ (sN {m} Nm) (sN {n} Nn) Sm<Sn Sn<Sm =
  x<y→y<x→⊥ Nm Nn (trans (sym (<-SS m n)) Sm<Sn) (trans (sym (<-SS n m)) Sn<Sm)
