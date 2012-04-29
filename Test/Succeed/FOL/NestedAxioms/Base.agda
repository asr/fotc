{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.NestedAxioms.Base where

infix 4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set

-- We need some ATP axiom to write down in the TPTP file.
postulate sym : ∀ d e → d ≡ e → e ≡ d
{-# ATP axiom sym #-}
