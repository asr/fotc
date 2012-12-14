------------------------------------------------------------------------------
-- Note on the equality type class
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from: On the Bright Side of Type Classes: Instances
-- Arguments in Agda (ICFP'11).


module FOT.FOTC.TypeClasses.Equality where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

∃-proj₁ : ∀ {A} → ∃ A → D
∃-proj₁ (x , _) = x

record Eq (A : D → Set) : Set where
  field equal : ∀ {t₁ t₂} → A t₁ → A t₂ → ∃ Bool

primBoolEquality : ∀ {b₁} {b₂} → Bool b₁ → Bool b₂ → ∃ Bool
primBoolEquality btrue  btrue  = true , btrue
primBoolEquality bfalse bfalse = true , btrue
primBoolEquality _      _      = false , bfalse

primNEquality : ∀ {m} {n} → N m → N n → ∃ Bool
primNEquality nzero      nzero      = true , btrue
primNEquality (nsucc Nm) (nsucc Nn) = primNEquality Nm Nn
primNEquality _          _          = false , bfalse

eqBool : Eq Bool
eqBool = record { equal = primBoolEquality }

eqN : Eq N
eqN = record { equal = primNEquality }

equal : {A : D → Set}{t₁ t₂ : D} → {{eqT : Eq A}} → A t₁ → A t₂ → ∃ Bool
equal {{eqT}} = Eq.equal eqT

test : D
test = ∃-proj₁ (equal nzero (nsucc nzero)) && ∃-proj₁ (equal bfalse bfalse)
