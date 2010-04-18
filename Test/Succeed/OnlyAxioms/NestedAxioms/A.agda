module Test.Succeed.OnlyAxioms.NestedAxioms.A where

infix 4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set
  a b : D

postulate
  a≡b : a ≡ b
{-# ATP axiom a≡b #-}
