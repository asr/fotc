------------------------------------------------------------------------------
-- Group theory base
------------------------------------------------------------------------------

module GroupTheory.Base where

-- We add 3 to the fixities of the standard library.
infix  11 _⁻¹
infixl 10 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------

-- The group universe
open import Common.Universe public renaming ( D to G )

-- The equality
-- The equality is the propositional identity on the group universe.

-- N.B. The following module is exported by this module.
open import Common.Relation.Binary.PropositionalEquality public

-- Logical constants
-- N.B. The module is exported by this module.
open import Common.LogicalConstants public

-- Group theory axioms
postulate
  ε   : G          -- The identity element.
  _·_ : G → G → G  -- The group binary operation.
  _⁻¹ : G → G      -- The inverse function.

  assoc         : ∀ x y z → x · y · z    ≡ x · (y · z)
  leftIdentity  : ∀ x     →     ε · x    ≡ x
  rightIdentity : ∀ x     →     x · ε    ≡ x
  leftInverse   : ∀ x     →  x ⁻¹ · x    ≡ ε
  rightInverse  : ∀ x     →  x    · x ⁻¹ ≡ ε
{-# ATP axiom assoc #-}
{-# ATP axiom leftIdentity #-}
{-# ATP axiom rightIdentity #-}
{-# ATP axiom leftInverse #-}
{-# ATP axiom rightInverse #-}
