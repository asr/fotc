------------------------------------------------------------------------------
-- Theory T from the paper
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module T where

infixl 9 _·_  -- The symbol is '\cdot'.
infix  7 _≡_

------------------------------------------------------------------------------

postulate
  T        : Set
  zero K S : T
  succ     : T → T
  _·_      : T → T → T

-- The identity type on the universe of discourse.
data _≡_ (x : T) : T → Set where
  refl : x ≡ x

-- Conversion rules
postulate
  cK : ∀ x y → K · x · y         ≡ x
  cS : ∀ x y z → S · x ·  y ·  z ≡ x ·  z ·  (y ·  z)
