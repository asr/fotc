{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.HigherOrder where

infixl 6 _∙_
infix  4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set
  lam : (D → D) → D
  _∙_ : D → D → D
  fix : (D → D) → D

-- Hack: In both translations we are quantifying on the variable 'f',
-- i.e. we are treating this variable as if it were of type D.

postulate cBeta : (f : D → D) → (a : D) → (lam f) ∙ a ≡ f a
{-# ATP axiom cBeta #-}

postulate cFix : (f : D → D) → fix f ≡ f (fix  f)
{-# ATP axiom cFix #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
