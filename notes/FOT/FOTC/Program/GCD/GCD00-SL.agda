------------------------------------------------------------------------------
-- In the standard library, gcd 0 0 = 0.
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.GCD.GCD00-SL where

open import Data.Nat.GCD
open import Data.Product
open import Relation.Binary.PropositionalEquality

open GCD hiding ( refl )

------------------------------------------------------------------------------

gcd00 : proj₁ (gcd 0 0) ≡ 0
gcd00 = refl

-- A different proof.
gcd00' : GCD 0 0 0
gcd00' = base
