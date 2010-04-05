module Test.Fail.NestedAxioms.B where

open import Test.Fail.NestedAxioms.A public

postulate
  b≡c : b ≡ c
{-# ATP axiom b≡c #-}
