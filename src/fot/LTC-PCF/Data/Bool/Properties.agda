------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Bool.Properties where

open import LTC-PCF.Base
open import LTC-PCF.Data.Bool
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.Properties
open import LTC-PCF.Data.Nat.Type

------------------------------------------------------------------------------
-- Congruence properties

notCong : ∀ {a b} → a ≡ b → not a ≡ not b
notCong refl = refl

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
&&-Bool {b = b} btrue  Bb = subst Bool (sym (t&&x≡x b)) Bb
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
x≢not-x btrue  h = t≢f (trans h not-t)
x≢not-x bfalse h = t≢f (sym (trans h not-f))

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive btrue  = trans (notCong not-t) not-f
not-involutive bfalse = trans (notCong not-f) not-t

------------------------------------------------------------------------------
-- Properties with inequalities

lt-Bool : ∀ {m n} → N m → N n → Bool (lt m n)
lt-Bool nzero          nzero          = subst Bool (sym lt-00) bfalse
lt-Bool nzero          (nsucc {n} Nn) = subst Bool (sym (lt-0S n)) btrue
lt-Bool (nsucc {m} Nm) nzero          = subst Bool (sym (lt-S0 m)) bfalse
lt-Bool (nsucc {m} Nm) (nsucc {n} Nn) = subst Bool (sym (lt-SS m n)) (lt-Bool Nm Nn)

le-Bool : ∀ {m n} → N m → N n → Bool (le m n)
le-Bool {n = n} nzero         Nn             = subst Bool (sym (lt-0S n)) btrue
le-Bool        (nsucc Nm)     nzero          = subst Bool (sym (Sx≰0 Nm)) bfalse
le-Bool        (nsucc {m} Nm) (nsucc {n} Nn) =
  subst Bool (sym (lt-SS m (succ₁ n))) (le-Bool Nm Nn)
