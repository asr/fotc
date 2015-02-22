------------------------------------------------------------------------------
-- Group theory base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module GroupTheory.Base where

infix  8 _⁻¹
infixl 7 _·_

------------------------------------------------------------------------------
-- First-order logic with equality.
open import Common.FOL.FOL-Eq public renaming ( D to G )

-- Group theory axioms
postulate
  ε   : G          -- The identity element.
  _·_ : G → G → G  -- The binary operation.
  _⁻¹ : G → G      -- The inverse function.

  -- We choose a non-redundant set of axioms. See for example (Mac
  -- Lane and Garret 1999, exercises 5-7, p. 50-51, or Hodges 1993,
  -- p. 37).
  assoc         : ∀ a b c → a · b · c ≡ a · (b · c)
  leftIdentity  : ∀ a → ε · a         ≡ a
  leftInverse   : ∀ a → a ⁻¹ · a      ≡ ε
{-# ATP axiom assoc leftIdentity leftInverse #-}

------------------------------------------------------------------------------
-- References
--
-- Hodges, W. (1993). Model Theory. Vol. 42. Encyclopedia of
-- Mathematics and its Applications. Cambridge University Press.
--
-- Mac Lane, S. and Birkhof, G. (1999). Algebra. 3rd ed. AMS Chelsea
-- Publishing.
