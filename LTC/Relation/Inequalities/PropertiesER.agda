------------------------------------------------------------------------------
-- Properties of the inequalities (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Relation.Inequalities.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Properties using ( x≥0 )
open import LTC.Data.N
open import MyStdLib.Data.Sum
open import MyStdLib.Function

------------------------------------------------------------------------------

¬0>x : {n : D} → N n → ¬ (GT zero n)
¬0>x Nn 0>n = true≠false $ trans (sym 0>n ) $ x≥0 Nn

¬S≤0 : {d : D} → ¬ (LE (succ d) zero)
¬S≤0 {d} Sx≤0 = true≠false $ trans (sym $ lt-0S d ) Sx≤0

x>y∨x≤y : {m n : D} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ lt-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  subst (λ a → a ≡ true ∨ a ≡ false)
        (sym $ lt-SS n m)
        (x>y∨x≤y Nm Nn )

¬x<x : {m : D} → N m → ¬ (LT m m)
¬x<x zN          0<0   = ⊥-elim (true≠false (trans (sym 0<0) lt-00))
¬x<x (sN {m} Nm) Sm<Sm = ⊥-elim (¬x<x Nm (trans (sym (lt-SS m m)) Sm<Sm))
