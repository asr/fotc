------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

module LTC.Data.Nat.Inequalities.Properties where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Elimination properties

¬0<0 : ¬ LT zero zero
¬0<0 0<0 = true≠false $ trans (sym 0<0) <-00

¬S<0 : {d : D} → ¬ LT (succ d) zero
¬S<0 {d} Sd<0 = true≠false $ trans (sym Sd<0) (<-S0 d)

¬x<0 : ∀ {n} → N n → ¬ (LT n zero)
¬x<0 zN     0<0  = ¬0<0 0<0
¬x<0 (sN _) Sn<0 = ¬S<0 Sn<0

¬x<x : ∀ {n} → N n → ¬ (LT n n)
¬x<x zN          0<0   = ¬0<0 0<0
¬x<x (sN {n} Nn) Sn<Sn = ⊥-elim $ ¬x<x Nn (trans (sym $ <-SS n n) Sn<Sn)

¬0>0 : ¬ GT zero zero
¬0>0 0>0 = true≠false $ trans (sym 0>0) <-00

¬0>S : {d : D} → ¬ GT zero (succ d)
¬0>S {d} 0>Sd = true≠false (trans (sym 0>Sd) (<-S0 d))

¬0>x : ∀ {n} → N n → ¬ (GT zero n)
¬0>x zN     0>0  = ¬0>0 0>0
¬0>x (sN _) 0>Sn = ¬0>S 0>Sn

¬x>x : ∀ {n} → N n → ¬ (GT n n)
¬x>x Nn = ¬x<x Nn

¬S≤0 : ∀ {n} → N n → ¬ (LE (succ n) zero)
¬S≤0 zN         S0≤0  = true≠false (trans (sym S0≤0)
                                          (trans (<-SS zero zero) <-00))
¬S≤0 (sN {n} _) SSn≤0 = true≠false (trans (sym SSn≤0)
                                          (trans (<-SS (succ n) zero) (<-S0 n)))

¬0≥S : ∀ {n} → N n → ¬ (GE zero (succ n))
¬0≥S Nn 0≥Sn = ¬S≤0 Nn 0≥Sn
