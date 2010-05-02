------------------------------------------------------------------------------
-- Properties of the inequalities (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Relation.Inequalities.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.PropertiesER
open import LTC.Relation.Inequalities
open import LTC.Data.N

open import MyStdLib.Data.Sum
open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module IPER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------

x≥0 : {n : D} → N n → GE n zero
x≥0 zN          = lt-00
x≥0 (sN {n} Nn) = lt-S0 n

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

x≤x+y : {m n : D} → N m → N n → LE m (m + n)
x≤x+y         zN          Nn = x≥0 (+-N zN Nn)
x≤x+y {n = n} (sN {m} Nm) Nn =
  begin
    lt (succ m + n) (succ m)   ≡⟨ subst (λ t → lt (succ m + n) (succ m) ≡
                                               lt t (succ m))
                                        (+-Sx m n)
                                        refl
                               ⟩
    lt (succ (m + n)) (succ m) ≡⟨ lt-SS (m + n) m ⟩
    lt (m + n) m               ≡⟨ x≤x+y Nm Nn ⟩
    false
  ∎
