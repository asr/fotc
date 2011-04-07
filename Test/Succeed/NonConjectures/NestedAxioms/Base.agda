module Test.Succeed.NonConjectures.NestedAxioms.Base where

infix 4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set

-- We need some ATP axiom to write down in the file Base.ax.
postulate
  refl : ∀ d → d ≡ d
{-# ATP axiom refl #-}
