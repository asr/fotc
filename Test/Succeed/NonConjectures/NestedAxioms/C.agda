module Test.Succeed.NonConjectures.NestedAxioms.C where

{-
Process this file should be generate a tptp file with the
following axioms

fof(..., axiom, ( ! [A] : ( A = A ) )
fof(..., axiom, ( a₁ = a₂ )).
fof(..., axiom, ( b₁ = b₂ )).
fof(..., axiom, ( c₁ = c₂ )).
-}

open import Test.Succeed.NonConjectures.NestedAxioms.Base using ( _≡_ ; D )

-- Only imported for to translate the axioms.
open import Test.Succeed.NonConjectures.NestedAxioms.B using ()

postulate
  c₁ c₂ : D
  c₁≡c₂ : c₁ ≡ c₂
{-# ATP axiom c₁≡c₂ #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate
  refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
