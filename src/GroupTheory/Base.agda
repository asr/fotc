------------------------------------------------------------------------------
-- Group theory base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GroupTheory.Base where

-- We add 3 to the fixities of the standard library.
infix  11 _⁻¹
infixl 10 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------
-- The group universe
open import Common.Universe public renaming ( D to G )

-- The equality
-- The equality is the propositional identity on the group universe.
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.Inductive public

-- Logical constants
open import Common.LogicalConstants public

-- Group theory axioms
postulate
  ε   : G          -- The identity element.
  _·_ : G → G → G  -- The binary operation.
  _⁻¹ : G → G      -- The inverse function.

  assoc         : ∀ x y z → x · y · z    ≡ x · (y · z)
  leftIdentity  : ∀ x     →     ε · x    ≡ x
  rightIdentity : ∀ x     →     x · ε    ≡ x
  leftInverse   : ∀ x     →  x ⁻¹ · x    ≡ ε
  rightInverse  : ∀ x     →  x    · x ⁻¹ ≡ ε
{-# ATP axiom assoc leftIdentity rightIdentity leftInverse rightInverse #-}
