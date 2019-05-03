------------------------------------------------------------------------------
-- Non-terminating GCD
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module FOT.FOTC.Program.GCD.GCD-NT where

open import Data.Nat
open import Relation.Nullary

------------------------------------------------------------------------------

{-# TERMINATING #-}
gcd : ℕ → ℕ → ℕ
gcd 0       0       = 0
gcd (suc m) 0       = suc m
gcd 0       (suc n) = suc n
gcd (suc m) (suc n) with suc m ≤? suc n
gcd (suc m) (suc n) | yes p = gcd (suc m) (suc n ∸ suc m)
gcd (suc m) (suc n) | no ¬p = gcd (suc m ∸ suc n) (suc n)
