------------------------------------------------------------------------------
-- We do not translate underscore variables
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Underscore where

infix 4 _≡_

postulate
  D    : Set
  zero : D
  succ : D → D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN : ∀ {n} → N n → N (succ n)

foo : ∀ m n → N m → N n → n ≡ n
foo m n _ _ = prf
  where
  postulate prf : n ≡ n
  {-# ATP prove prf #-}
