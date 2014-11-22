{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Type classes following Kettelhoit's approach.

module Kettelhoit where

open import Data.Bool
open import Data.Nat hiding ( equal ) renaming ( suc to succ )

record Eq (A : Set) : Set where
  field equal : A → A → Bool

open Eq {{...}} public

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

instance
  eqInstanceBool : Eq Bool
  eqInstanceBool = record { equal = boolEq }

  eqInstanceℕ : Eq ℕ
  eqInstanceℕ = record { equal = natEq }

test : Bool
test = equal 5 3 ∨ equal true false
