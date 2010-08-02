module Test.Succeed.NonConjectures.NestedAxioms.C where

{-
Process this file should be generate a file general-roles.tptp with the
following axioms

fof(..., axiom, ( a = b )).
fof(..., axiom, ( b = c )).
fof(..., axiom, ( c = d )).
-}

open import Test.Succeed.NonConjectures.NestedAxioms.A
open import Test.Succeed.NonConjectures.NestedAxioms.B

postulate
  d : D

postulate
  c≡d : c ≡ d
{-# ATP axiom c≡d #-}
