module Test.Succeed.NonConjectures.NestedAxioms.B where

open import Test.Succeed.NonConjectures.NestedAxioms.A

postulate
  c : D

postulate
  b≡c : b ≡ c
{-# ATP axiom b≡c #-}
