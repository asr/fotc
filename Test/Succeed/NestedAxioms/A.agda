module Test.Succeed.NestedAxioms.A where

open import Test.Succeed.NestedAxioms.Base using ( _≡_ ; D )

postulate
  a₁ a₂ : D
  a₁≡a₂ : a₁ ≡ a₂
{-# ATP axiom a₁≡a₂ #-}
