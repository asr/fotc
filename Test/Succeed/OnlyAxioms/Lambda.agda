module Test.Succeed.OnlyAxioms.Lambda where

infixl 6 _∙_
infix  4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set
  lam : (D → D) → D
  _∙_ : D → D → D
  succ : D → D


postulate
  -- Hack: In the translation we are quantifying on the variable 'f',
  -- i.e. we are treating this variable as if it were of type D.
  cBeta : (f : D → D) → (a : D) → (lam f) ∙ a ≡ f a
{-# ATP axiom cBeta #-}
