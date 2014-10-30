------------------------------------------------------------------------------
-- A proof that was rejected using the --without-K option
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module ListsSL where

open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Relation.Binary
module NDTO = DecTotalOrder decTotalOrder

------------------------------------------------------------------------------

LTC : {A : Set} → List A → List A → Set
LTC xs ys = ∃ (λ x → ys ≡ x ∷ xs)

LTL : {A : Set} → List A → List A → Set
LTL xs ys = (length xs) < (length ys)

helper : {A : Set}(y : A)(xs : List A) → (length xs) < (length (y ∷ xs))
helper y []       = s≤s z≤n
helper y (x ∷ xs) = s≤s NDTO.refl

-- 25 April 2014. The proof is accepted using Cockx's --without-K
-- implementation.
foo : {A : Set}(xs ys : List A) → LTC xs ys → LTL xs ys
foo xs .(x ∷ xs) (x , refl) = helper x xs

foo' : {A : Set}(xs ys : List A) → LTC xs ys → LTL xs ys
foo' xs ys (x , h) =
  subst (λ ys' → length xs < length ys') (sym h) (helper x xs)
