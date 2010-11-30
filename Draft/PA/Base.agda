------------------------------------------------------------------------------
-- Peano arithmetic base
------------------------------------------------------------------------------

module Draft.PA.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_

------------------------------------------------------------------------------
-- PA universe
-- N.B. The following module is exported by this module.
open import Common.Universe public renaming ( D to PA )

-- Logical constants
-- N.B. The module is exported by this module.
open import Common.LogicalConstants public

-- Non-logical constants
postulate
  zero : PA
  succ : PA → PA
  _+_  : PA → PA → PA
  _*_  : PA → PA → PA

-- The PA equality
-- The PA equality is the propositional identity on the PA universe.
-- N.B. The following modules are exported by this module.
-- N.B. We are not using the refl and sym properties because they are
-- not stated in the proper axioms (see below).
open import Common.Relation.Binary.PropositionalEquality public
  using ( _≡_ )
open import Common.Relation.Binary.PropositionalEquality.Properties public
  using ( trans )

-- Proper axioms
-- (From Elliott Mendelson. Introduction to mathematical
-- logic. Chapman & Hall, 4th edition, 1997, p. 155)

-- S₁. x₁ = x₂ → x₁ = x₃ → x₂ = x₃
-- S₂. x₁ = x₂ → succ x₁ = succ x₂
-- S₃. 0 ≠ succ x
-- S₄. succ x₁ = succ x₂ → x₁ = x₂
-- S₅. x₁ + 0 = x₁
-- S₆. x₁ + succ x₂ = succ (x₁ + x₂)
-- S₇. x₁ * 0 = 0
-- S₈. x₁ * succ x₂ = (x₁ * x₂) + x₁
-- S₉. P(0) → (∀x.P(x) → P(succ x)) → ∀x.P(x)

postulate
  -- S₁: This axiom is the transitivity property imported from
  --     Common.Relation.Binary.PropositionalEquality.Properties.

  -- S₂: This axiom is not required by the ATPs.

  S₃ : ∀ {x} → ¬ (zero ≡ succ x)

  S₄ : ∀ {x₁ x₂} → succ x₁ ≡ succ x₂ → x₁ ≡ x₂

  S₅ : ∀ x →     zero    + x  ≡ x
  S₆ : ∀ x₁ x₂ → succ x₁ + x₂ ≡ succ (x₁ + x₂)

  S₇ : ∀ x →     zero    * x  ≡ zero
  S₈ : ∀ x₁ x₂ → succ x₁ * x₂ ≡ x₂ + x₁ * x₂

  -- S₉: Instead of the induction schema we will use the inductive predicate N
  --     (see Draft.PA.Type).

{-# ATP axiom S₃ #-}
{-# ATP axiom S₄ #-}
{-# ATP axiom S₅ #-}
{-# ATP axiom S₆ #-}
{-# ATP axiom S₇ #-}
{-# ATP axiom S₈ #-}
