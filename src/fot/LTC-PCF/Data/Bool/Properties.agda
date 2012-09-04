------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Bool.Properties where

open import LTC-PCF.Base
open import LTC-PCF.Data.Bool
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.Properties
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
&&-Bool {b = b} btrue  Bb = subst Bool (sym (t&&x≡x b )) Bb
&&-Bool {b = b} bfalse Bb = subst Bool (sym (f&&x≡f b)) bfalse

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool btrue  = subst Bool (sym not-t) bfalse
not-Bool bfalse = subst Bool (sym not-f) btrue

&&-comm : ∀ {a b} → Bool a → Bool b → a && b ≡ b && a
&&-comm btrue  btrue  = refl
&&-comm btrue  bfalse = trans (t&&x≡x false) (sym (f&&x≡f true))
&&-comm bfalse btrue  = trans (f&&x≡f true) (sym (t&&x≡x false))
&&-comm bfalse bfalse = refl

x≢not-x : ∀ {b} → Bool b → b ≢ not b
x≢not-x btrue  h = true≢false (trans h not-t)
x≢not-x bfalse h = true≢false (sym (trans h not-f))

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive btrue  = trans (cong not not-t) not-f
not-involutive bfalse = trans (cong not not-f) not-t

------------------------------------------------------------------------------
-- Properties with inequalities

<-Bool : ∀ {m n} → N m → N n → Bool (m < n)
<-Bool nzero          nzero          = subst Bool (sym <-00) bfalse
<-Bool nzero          (nsucc {n} Nn) = subst Bool (sym (<-0S n)) btrue
<-Bool (nsucc {m} Nm) nzero          = subst Bool (sym (<-S0 m)) bfalse
<-Bool (nsucc {m} Nm) (nsucc {n} Nn) = subst Bool (sym (<-SS m n)) (<-Bool Nm Nn)

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} nzero         Nn             = subst Bool (sym (<-0S n)) btrue
≤-Bool        (nsucc Nm)     nzero          = subst Bool (sym (Sx≰0 Nm)) bfalse
≤-Bool        (nsucc {m} Nm) (nsucc {n} Nn) =
  subst Bool (sym (<-SS m (succ₁ n))) (≤-Bool Nm Nn)
