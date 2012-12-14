------------------------------------------------------------------------------
-- Note on type classes
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.TypeClasses.Test where

open import FOTC.Base
open import FOTC.Data.List.Type
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

-- 14 December 2012. Type classes for FOTC means type classes for the
-- inductive predicates because them represent the Haskell types. In this
-- case, we are not working in first-order logic.

data _≈_ {A : Set₁}(x : A) : A → Set₁ where
  refl : x ≈ x

foo : ∀ {m n} → m ≡ n → N m ≈ N n
foo refl = refl

bar : ∀ {xs ys} → xs ≡ ys → List xs ≈ List ys
bar refl = refl
