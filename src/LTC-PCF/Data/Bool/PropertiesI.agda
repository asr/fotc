------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Bool.PropertiesI where

open import LTC-PCF.Base
open import LTC-PCF.Data.Bool
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
open import LTC-PCF.Data.Nat.Type

------------------------------------------------------------------------------
-- Basic properties

t&&x≡x : ∀ b → true && b ≡ b
t&&x≡x b = if-true b

f&&x≡f : ∀ b → false && b ≡ false
f&&x≡f b = if-false false

not-t : not true ≡ false
not-t = if-true false

not-f : not false ≡ true
not-f = if-false true

&&-Bool : ∀ {a b} → Bool a → Bool b → Bool (a && b)
&&-Bool {b = b} tB Bb = subst Bool (sym (t&&x≡x b )) Bb
&&-Bool {b = b} fB Bb = subst Bool (sym (f&&x≡f b)) fB

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool tB = subst Bool (sym not-t) fB
not-Bool fB = subst Bool (sym not-f) tB

x≢not-x : ∀ {b} → Bool b → b ≢ not b
x≢not-x tB h = true≢false (trans h not-t)
x≢not-x fB h = true≢false (sym (trans h not-f))

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive tB = trans (cong not not-t) not-f
not-involutive fB = trans (cong not not-f) not-t

------------------------------------------------------------------------------
-- Properties with inequalities

<-Bool : ∀ {m n} → N m → N n → Bool (m < n)
<-Bool zN          zN          = subst Bool (sym <-00) fB
<-Bool zN          (sN {n} Nn) = subst Bool (sym (<-0S n)) tB
<-Bool (sN {m} Nm) zN          = subst Bool (sym (<-S0 m)) fB
<-Bool (sN {m} Nm) (sN {n} Nn) = subst Bool (sym (<-SS m n)) (<-Bool Nm Nn)

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN         Nn          = subst Bool (sym (<-0S n)) tB
≤-Bool        (sN Nm)     zN          = subst Bool (sym (Sx≰0 Nm)) fB
≤-Bool        (sN {m} Nm) (sN {n} Nn) =
  subst Bool (sym (<-SS m (succ₁ n))) (≤-Bool Nm Nn)
