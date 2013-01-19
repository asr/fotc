------------------------------------------------------------------------------
-- Note on the equality type class using instance arguments
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from: On the Bright Side of Type Classes: Instances
-- Arguments in Agda (ICFP'11).

module FOT.FOTC.TypeClasses.EqualityInstanceArguments where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

∃-proj₁ : ∀ {A} → ∃ A → D
∃-proj₁ (x , _) = x

record Eq (P : D → Set) : Set₁ where
  field equal : ∀ {t₁ t₂} → P t₁ → P t₂ → Set

equal : {P : D → Set}{t₁ t₂ : D} → {{eqT : Eq P}} → P t₁ → P t₂ → Set
equal {{eqT}} = Eq.equal eqT

boolEq : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → Set
boolEq btrue  btrue  = Bool true
boolEq bfalse bfalse = Bool true
boolEq _      _      = Bool false

nEq : ∀ {m n} → N m → N n → Set
nEq nzero      nzero      = Bool true
nEq (nsucc Nm) (nsucc Nn) = Bool true
nEq _          _          = Bool false

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
