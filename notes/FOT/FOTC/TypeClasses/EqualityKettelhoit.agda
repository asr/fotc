------------------------------------------------------------------------------
-- Note on the equality type class using Kettelhoit's approach
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from Kettelhoit's thesis.

module FOT.FOTC.TypeClasses.EqualityKettelhoit where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

∃-proj₁ : ∀ {A} → ∃ A → D
∃-proj₁ (x , _) = x

record Eq (A : D → Set) : Set where
  field equal : ∀ {t₁ t₂} → A t₁ → A t₂ → ∃ Bool

open Eq {{...}} public

boolEq : ∀ {b₁} {b₂} → Bool b₁ → Bool b₂ → ∃ Bool
boolEq btrue  btrue  = true , btrue
boolEq bfalse bfalse = true , btrue
boolEq _      _      = false , bfalse

nEq : ∀ {m} {n} → N m → N n → ∃ Bool
nEq nzero      nzero      = true , btrue
nEq (nsucc Nm) (nsucc Nn) = nEq Nm Nn
nEq _          _          = false , bfalse

eqInstanceBool : Eq Bool
eqInstanceBool = record { equal = boolEq }

eqInstanceN : Eq N
eqInstanceN = record { equal = nEq }

test : D
test = ∃-proj₁ (equal nzero (nsucc nzero)) && ∃-proj₁ (equal bfalse bfalse)
