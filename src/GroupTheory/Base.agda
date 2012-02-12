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

  assoc         : ∀ a b c → a · b · c    ≡ a · (b · c)
  leftIdentity  : ∀ a     →     ε · a    ≡ a
  rightIdentity : ∀ a     →     a · ε    ≡ a
  leftInverse   : ∀ a     →  a ⁻¹ · a    ≡ ε
  rightInverse  : ∀ a     →  a    · a ⁻¹ ≡ ε
{-# ATP axiom assoc leftIdentity rightIdentity leftInverse rightInverse #-}

-- Congruence property.
·-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ ≡ y₂ → x₁ · x₂ ≡ y₁ · y₂
·-cong = cong₂ _·_
