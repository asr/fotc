------------------------------------------------------------------------------
-- Testing nested axioms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module NestedAxioms.B where

open import NestedAxioms.A

------------------------------------------------------------------------------

postulate
  c : D
  b≡c : b ≡ c
{-# ATP axiom b≡c #-}
