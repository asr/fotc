module test.NestedAxioms.B where

open import test.NestedAxioms.A public

postulate
  b≡c : b ≡ c
{-# ATP axiom b≡c #-}
