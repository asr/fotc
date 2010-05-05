------------------------------------------------------------------------------
-- Properties of the inequalities (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Relation.Inequalities.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties using ( +-comm )
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

x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m
x>y→x-y+y≡x zN          Nn 0>n  = ⊥-elim (¬0>x Nn 0>n)
x>y→x-y+y≡x (sN {m} Nm) zN Sm>0 = trans (+-rightIdentity (minus-N (sN Nm) zN))
                                        (minus-x0 (succ m))
x>y→x-y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  begin
    (succ m - succ n) + succ n ≡⟨ subst (λ t → (succ m - succ n) + succ n ≡
                                               t + succ n)
                                        (minus-SS m n)
                                        refl
                               ⟩
    (m - n) + succ n           ≡⟨ +-comm (minus-N Nm Nn) (sN Nn) ⟩
    succ n + (m - n)           ≡⟨ +-Sx n (m - n) ⟩
    succ (n + (m - n))         ≡⟨ subst (λ t → succ (n + (m - n)) ≡ succ t )
                                        (+-comm Nn (minus-N Nm Nn))
                                        refl
                               ⟩
    succ ((m - n) + n)         ≡⟨ subst (λ t → succ ((m - n) + n) ≡ succ t )
                                        (x>y→x-y+y≡x Nm Nn
                                             (trans (sym (lt-SS n m)) Sm>Sn) )
                                        refl
                               ⟩
    succ m
  ∎
