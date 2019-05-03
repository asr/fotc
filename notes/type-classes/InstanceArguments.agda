{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

-- From: On the Bright Side of Type Classes: Instances Arguments in
-- Agda (ICFP'11).

module InstanceArguments where

open import Data.Bool.Base
open import Data.Nat hiding ( equal ) renaming ( suc to succ )

-- Note: Agda doesn't have a primitive function primBoolEquality.
boolEq : Bool → Bool → Bool
boolEq true  true  = true
boolEq false false = true
{-# CATCHALL #-}
boolEq _     _     = false

natEq : ℕ → ℕ → Bool
natEq zero  zero         = true
natEq (succ m) (succ n)  = natEq m n
{-# CATCHALL #-}
natEq _     _            = false

record Eq (t : Set) : Set where
  field equal : t → t → Bool

instance
  eqInstanceBool : Eq Bool
  eqInstanceBool = record { equal = boolEq }

  eqInstanceℕ : Eq ℕ
  eqInstanceℕ = record { equal = natEq }

equal : {t : Set} → {{eqT : Eq t}} → t → t → Bool
equal {{eqT}} = Eq.equal eqT

test : Bool
test = equal 5 3 ∨ equal true false
