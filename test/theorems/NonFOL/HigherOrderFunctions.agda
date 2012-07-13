------------------------------------------------------------------------------
-- Testing the translation of higher-order functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-functions #-}
{-# OPTIONS --without-K #-}

-- We can use the Agda pragma @--universal-quantified-functions@ to
-- translate higher-order functions. The canonical examples are the
-- conversion rules for the λ-abstraction and the fixed-point
-- operator.

module NonFOL.HigherOrderFunctions where

infixl 6 _∙_
infix  4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set
  lam : (D → D) → D
  _∙_ : D → D → D
  fix : (D → D) → D

postulate beta : (f : D → D) → (a : D) → (lam f) ∙ a ≡ f a
{-# ATP axiom beta #-}

postulate fix-f : (f : D → D) → fix f ≡ f (fix  f)
{-# ATP axiom fix-f #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
