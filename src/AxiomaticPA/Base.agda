------------------------------------------------------------------------------
-- Peano arithmetic base
------------------------------------------------------------------------------

module AxiomaticPA.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_

------------------------------------------------------------------------------
-- PA universe
-- N.B. The following module is exported by this module.
open import Common.Universe public renaming ( D to ℕ )

-- Logical constants
-- N.B. The module is exported by this module.
open import Common.LogicalConstants public

-- Non-logical constants
postulate
  zero : ℕ
  succ : ℕ → ℕ
  _+_  : ℕ → ℕ → ℕ
  _*_  : ℕ → ℕ → ℕ

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
-- S₉. P(0) → (∀x.P(x) → P(succ x)) → ∀x.P(x), for any wf P(x) of PA.

postulate
  -- S₁: This axiom is the transitivity property imported from
  --     Common.Relation.Binary.PropositionalEquality.Properties.

  -- S₂: This axiom is not required by the ATPs.

  S₃ : ∀ {n} → ¬ (zero ≡ succ n)

  S₄ : ∀ {m n} → succ m ≡ succ n → m ≡ n

  S₅ : ∀ n →   zero   + n ≡ n
  S₆ : ∀ m n → succ m + n ≡ succ (m + n)

  S₇ : ∀ n →   zero   * n ≡ zero
  S₈ : ∀ m n → succ m * n ≡ m + n * m

  -- N.B. S₉ is a higher-order axiom, therefore we do not translate it
  -- as an ATP axiom.
  S₉ : (P : ℕ → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n

{-# ATP axiom S₃ #-}
{-# ATP axiom S₄ #-}
{-# ATP axiom S₅ #-}
{-# ATP axiom S₆ #-}
{-# ATP axiom S₇ #-}
{-# ATP axiom S₈ #-}
