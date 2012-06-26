------------------------------------------------------------------------------
-- Testing nested axioms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

{-

Processing this file should be generate a TPTP file with the following
axioms

fof(..., axiom, ( a = b )).
fof(..., axiom, ( b = c )).
fof(..., axiom, ( c = d )).
-}

module Test.Succeed.FOL.NestedAxioms.C where

open import Test.Succeed.FOL.NestedAxioms.A
open import Test.Succeed.FOL.NestedAxioms.B

------------------------------------------------------------------------------

postulate
  d : D
  c≡d : c ≡ d
{-# ATP axiom c≡d #-}

postulate foo : d ≡ a
{-# ATP prove foo #-}
