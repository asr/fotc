------------------------------------------------------------------------------
-- Group theory base
------------------------------------------------------------------------------

module Examples.GroupTheory.Base where

-- We add 3 to the fixities of the standard library.
infix  11 _⁻¹
infixl 10 _∙_

------------------------------------------------------------------------------

-- The group universe
open import Common.Universe public renaming ( D to G )

-- The equality
-- The equality is the propositional identity on the group domain

-- N.B. The following modules are exported by this module.
open import Common.Relation.Binary.PropositionalEquality public
open import Common.Relation.Binary.PropositionalEquality.Properties public

-- Logical constants

-- N.B. The module is exported by this module.
open import Common.LogicalConstants public

postulate
  ε   : G          -- The identity element.
  _∙_ : G → G → G  -- The group binary operation.
  _⁻¹ : G → G      -- The inverse function.

-- Group theory axioms
postulate
   associativity : (x y z : G) → x ∙ y ∙ z ≡ x ∙ (y ∙ z)
   leftIdentity  : (x : G)     →     ε ∙ x ≡ x
   rightIdentity : (x : G)     →     x ∙ ε ≡ x
   leftInverse   : (x : G)     →  x ⁻¹ ∙ x ≡ ε
   rightInverse  : (x : G)     →  x ∙ x ⁻¹ ≡ ε
{-# ATP axiom associativity #-}
{-# ATP axiom leftIdentity #-}
{-# ATP axiom rightIdentity #-}
{-# ATP axiom leftInverse #-}
{-# ATP axiom rightInverse #-}
