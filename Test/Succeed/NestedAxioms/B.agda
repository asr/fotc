{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.NestedAxioms.B where

open import Test.Succeed.NestedAxioms.Base using ( _≡_ ; D )

-- Only imported for to translate the axioms.
open import Test.Succeed.NestedAxioms.A using ()

postulate
  b₁ b₂ : D
  b₁≡b₂ : b₁ ≡ b₂
{-# ATP axiom b₁≡b₂ #-}
