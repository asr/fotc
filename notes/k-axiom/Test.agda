-- {-# OPTIONS --without-K #-}

module Test where

open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality

-- 30 May 2013. The proof is rejected using the --without-K option.
foo : ∀ m n → m * n ≡ zero → m ≡ zero ⊎ n ≡ zero
foo zero     n      h = inj₁ refl
foo (suc m) zero    h = inj₂ refl
foo (suc m) (suc n) ()
