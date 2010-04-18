module Test.Succeed.OnlyAxioms.NestedAxioms.B where

open import Test.Succeed.OnlyAxioms.NestedAxioms.A

postulate
  c : D

postulate
  b≡c : b ≡ c
{-# ATP axiom b≡c #-}
