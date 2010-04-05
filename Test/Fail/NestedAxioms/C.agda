module Test.Fail.NestedAxioms.C where

{-
Process this file should be genereate a file axioms.tptp with the
following axioms

fof(..., axiom, ( a = b )).
fof(..., axiom, ( b = c )).
fof(..., axiom, ( c = d )).
-}

open import Test.Fail.NestedAxioms.B

postulate
  c≡d : c ≡ d
{-# ATP axiom c≡d #-}
