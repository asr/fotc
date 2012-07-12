------------------------------------------------------------------------------
-- Testing the use of implicit arguments
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The dot in the name of the implicit arguments must be removed.

module ImplicitArguments where

postulate
  D   : Set
  a b : D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate a≡b : a ≡ b
{-# ATP axiom a≡b #-}

foo : {n : D} → b ≡ a
foo = prf
  where
  postulate prf : b ≡ a
  {-# ATP prove prf #-}
