------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Bool.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Bool
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.Properties
open import Combined.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Basic properties

&&-Bool : ∀ {a b} → Bool a → Bool b → Bool (a && b)
&&-Bool {b = b} btrue Bb = prf
  where postulate prf : Bool (true && b)
        {-# ATP prove prf #-}
&&-Bool {b = b} bfalse Bb = prf
  where postulate prf : Bool (false && b)
        {-# ATP prove prf #-}

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool btrue = prf
  where postulate prf : Bool (not true)
        {-# ATP prove prf #-}
not-Bool bfalse = prf
  where postulate prf : Bool (not false)
        {-# ATP prove prf #-}

&&-list₂-t : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true ∧ b ≡ true
&&-list₂-t btrue btrue h = prf
  where postulate prf : true ≡ true ∧ true ≡ true
        {-# ATP prove prf #-}
&&-list₂-t btrue bfalse h = prf
  where postulate prf : true ≡ true ∧ false ≡ true
        {-# ATP prove prf #-}
&&-list₂-t bfalse btrue h = prf
  where postulate prf : false ≡ true ∧ true ≡ true
        {-# ATP prove prf #-}
&&-list₂-t bfalse bfalse h = prf
  where postulate prf : false ≡ true ∧ false ≡ true
        {-# ATP prove prf #-}

&&-list₂-t₁ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true
&&-list₂-t₁ {a} Ba Bb h = prf
  where postulate prf : a ≡ true
        {-# ATP prove prf &&-list₂-t #-}

&&-list₂-t₂ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → b ≡ true
&&-list₂-t₂ {b = b} Ba Bb h = prf
  where postulate prf : b ≡ true
        {-# ATP prove prf &&-list₂-t #-}

&&-list₄-t : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
             a && b && c && d ≡ true →
             a ≡ true ∧ b ≡ true ∧ c ≡ true ∧ d ≡ true
&&-list₄-t btrue btrue btrue btrue h = prf
  where postulate prf : true ≡ true ∧ true ≡ true ∧ true ≡ true ∧ true ≡ true
        {-# ATP prove prf #-}
&&-list₄-t btrue btrue btrue bfalse h = prf
  where postulate prf : true ≡ true ∧ true ≡ true ∧ true ≡ true ∧ false ≡ true
        {-# ATP prove prf #-}
&&-list₄-t {d = d} btrue btrue bfalse Bd h = prf
  where postulate prf : true ≡ true ∧ true ≡ true ∧ false ≡ true ∧ d ≡ true
        {-# ATP prove prf #-}
&&-list₄-t {c = c} {d} btrue bfalse Bc Bd h = prf
  where postulate prf : true ≡ true ∧ false ≡ true ∧ c ≡ true ∧ d ≡ true
        {-# ATP prove prf #-}
&&-list₄-t {b = b} {c} {d} bfalse Bb Bc Bd h = prf
  where postulate prf : false ≡ true ∧ b ≡ true ∧ c ≡ true ∧ d ≡ true
        {-# ATP prove prf #-}

&&-list₄-t₁ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → a ≡ true
&&-list₄-t₁ {a} Ba Bb Bc Bd h = prf
  where postulate prf : a ≡ true
        {-# ATP prove prf &&-list₄-t #-}

&&-list₄-t₂ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → b ≡ true
&&-list₄-t₂ {b = b} Ba Bb Bc Bd h = prf
  where postulate prf : b ≡ true
        {-# ATP prove prf &&-list₄-t #-}

&&-list₄-t₃ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → c ≡ true
&&-list₄-t₃ {c = c} Ba Bb Bc Bd h = prf
  where postulate prf : c ≡ true
        {-# ATP prove prf &&-list₄-t #-}

&&-list₄-t₄ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → d ≡ true
&&-list₄-t₄ {d = d} Ba Bb Bc Bd h = prf
  where postulate prf : d ≡ true
        {-# ATP prove prf &&-list₄-t #-}

x≢not-x : ∀ {b} → Bool b → b ≢ not b
x≢not-x btrue h = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
x≢not-x bfalse h = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = prf
  where postulate prf : ⊥
        {-# ATP prove prf x≢not-x #-}

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive btrue = prf
  where postulate prf : not (not true) ≡ true
        {-# ATP prove prf #-}
not-involutive bfalse = prf
  where postulate prf : not (not false) ≡ false
        {-# ATP prove prf #-}

------------------------------------------------------------------------------
-- Properties with inequalities

lt-Bool : ∀ {m n} → N m → N n → Bool (lt m n)
lt-Bool nzero nzero = prf
  where postulate prf : Bool (lt zero zero)
        {-# ATP prove prf #-}
lt-Bool nzero (nsucc {n} Nn) = prf
  where postulate prf : Bool (lt zero (succ₁ n))
        {-# ATP prove prf #-}
lt-Bool (nsucc {m} Nm) nzero = prf
  where postulate prf : Bool (lt (succ₁ m)  zero)
        {-# ATP prove prf #-}
lt-Bool (nsucc {m} Nm) (nsucc {n} Nn) = prf (lt-Bool Nm Nn)
  where postulate prf : Bool (lt m n) → Bool (lt (succ₁ m) (succ₁ n))
        {-# ATP prove prf #-}

le-Bool : ∀ {m n} → N m → N n → Bool (le m n)
le-Bool {n = n} nzero Nn = prf
  where postulate prf : Bool (le zero n)
        {-# ATP prove prf #-}
le-Bool (nsucc {m} Nm) nzero = prf
  where postulate prf : Bool (le (succ₁ m) zero)
        {-# ATP prove prf Sx≰0 #-}
le-Bool (nsucc {m} Nm) (nsucc {n} Nn) = prf (le-Bool Nm Nn)
  where postulate prf : Bool (le m n) → Bool (le (succ₁ m) (succ₁ n))
        {-# ATP prove prf #-}
