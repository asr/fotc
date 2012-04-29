{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.NestedAxioms.A where

open import Test.Succeed.FOL.NestedAxioms.Base using ( _≡_ ; D )

postulate
  a₁ a₂ : D
  a₁≡a₂ : a₁ ≡ a₂
{-# ATP axiom a₁≡a₂ #-}
