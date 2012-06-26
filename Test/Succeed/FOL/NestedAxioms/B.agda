------------------------------------------------------------------------------
-- Testing nested axioms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.NestedAxioms.B where

open import Test.Succeed.FOL.NestedAxioms.A

------------------------------------------------------------------------------

postulate
  c : D
  b≡c : b ≡ c
{-# ATP axiom b≡c #-}
