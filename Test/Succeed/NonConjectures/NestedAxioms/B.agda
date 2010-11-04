module Test.Succeed.NonConjectures.NestedAxioms.B where

open import Test.Succeed.NonConjectures.NestedAxioms.Base using ( _≡_ ; D )

-- Only imported for to translate the axioms.
open import Test.Succeed.NonConjectures.NestedAxioms.A using ()

postulate
  b₁ b₂ : D
  b₁≡b₂ : b₁ ≡ b₂
{-# ATP axiom b₁≡b₂ #-}
