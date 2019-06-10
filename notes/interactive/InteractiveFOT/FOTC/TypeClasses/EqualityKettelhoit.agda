------------------------------------------------------------------------------
-- Note on the equality type class using Kettelhoit's approach
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Adapted from Kettelhoit's thesis.

module InteractiveFOT.FOTC.TypeClasses.EqualityKettelhoit where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.Bool.Type
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------

record Eq (P : D → Set) : Set₁ where
  field equal : ∀ {t₁ t₂} → P t₁ → P t₂ → Set

open Eq {{...}} public

boolEq : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → Set
boolEq btrue  btrue  = Bool true
boolEq bfalse bfalse = Bool true
{-# CATCHALL #-}
boolEq _      _      = Bool false

nEq : ∀ {m n} → N m → N n → Set
nEq nzero      nzero      = Bool true
nEq (nsucc Nm) (nsucc Nn) = Bool true
{-# CATCHALL #-}
nEq _          _          = Bool false

instance
  eqInstanceBool : Eq Bool
  eqInstanceBool = record { equal = boolEq }

  eqInstanceN : Eq N
  eqInstanceN = record { equal = nEq }

test₁ : Set
test₁ = equal nzero (nsucc nzero)

test₂ : Set
test₂ = equal bfalse bfalse

eqN-sym : ∀ {m n} → (Nm : N m) → (Nn : N n) → equal Nm Nn → equal Nn Nm
eqN-sym nzero      nzero      h = h
eqN-sym nzero      (nsucc Nn) h = h
eqN-sym (nsucc Nm) nzero      h = h
eqN-sym (nsucc Nm) (nsucc Nn) h = h

postulate eqN-sym' : ∀ {m n} → (Nm : N m) → (Nn : N n) → equal Nm Nn → equal Nn Nm
-- {-# ATP prove eqN-sym' #-}
