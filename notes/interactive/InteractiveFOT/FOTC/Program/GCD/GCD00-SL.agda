------------------------------------------------------------------------------
-- In the Agda standard library, gcd 0 0 = 0.
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module InteractiveFOT.FOTC.Program.GCD.GCD00-SL where

open import Data.Nat.GCD
open import Data.Product
open import Relation.Binary.PropositionalEquality

open GCD hiding ( refl )

------------------------------------------------------------------------------

gcd00 : gcd 0 0 ≡ 0
gcd00 = refl

-- A different proof.
gcd00₂ : proj₁ (mkGCD 0 0) ≡ 0
gcd00₂ = refl

-- Other different proof.
gcd00₃ : GCD 0 0 0
gcd00₃ = base
