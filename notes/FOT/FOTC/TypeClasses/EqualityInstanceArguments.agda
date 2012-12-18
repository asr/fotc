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

record Eq (A : D → Set) : Set where
  field equal : ∀ {t₁ t₂} → A t₁ → A t₂ → ∃ Bool

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

equal : {A : D → Set}{t₁ t₂ : D} → {{eqT : Eq A}} → A t₁ → A t₂ → ∃ Bool
equal {{eqT}} = Eq.equal eqT

test : D
test = ∃-proj₁ (equal nzero (nsucc nzero)) && ∃-proj₁ (equal bfalse bfalse)
