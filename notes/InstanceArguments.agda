{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: On the Bright Side of Type Classes: Instances Arguments in
-- Agda (ICFP'11).

module InstanceArguments where

open import Data.Bool
open import Data.Nat hiding ( equal )

-- Note: Agda doesn't have a primitive function primBoolEquality
primBoolEquality : Bool → Bool → Bool
primBoolEquality true  true  = true
primBoolEquality false false = true
primBoolEquality _     _     = false

primitive
  primNatEquality : ℕ → ℕ → Bool

record Eq (t : Set) : Set where
  field equal : t → t → Bool

eqBool : Eq Bool
eqBool = record { equal = primBoolEquality }

eqℕ : Eq ℕ
eqℕ = record { equal = primNatEquality }

equal : {t : Set} → {{eqT : Eq t}} → t → t → Bool
equal {{eqT}} = Eq.equal eqT

test : Bool
test = equal 5 3 ∨ equal true false
