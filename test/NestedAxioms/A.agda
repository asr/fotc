module test.NestedAxioms.A where

infix 4 _≡_

postulate
  D : Set
  a b c d : D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate
  a≡b : a ≡ b
{-# ATP axiom a≡b #-}
