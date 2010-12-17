------------------------------------------------------------------------------
-- Peano arithmetic base
------------------------------------------------------------------------------

module AxiomaticPA.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infix  7  _≣_
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

-- The PA equality.
postulate
  _≣_ : ℕ → ℕ → Set

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
  S₁ : ∀ {m n o} → m ≣ n → m ≣ o → n ≣ o
{-# ATP axiom S₁ #-}

postulate
  S₂ : ∀ {m n} → m ≣ n → succ m ≣ succ n
{-# ATP axiom S₂ #-}

postulate
  S₃ : ∀ {n} → ¬ (zero ≣ succ n)
{-# ATP axiom S₃ #-}

postulate
  S₄ : ∀ {m n} → succ m ≣ succ n → m ≣ n
{-# ATP axiom S₄ #-}

-- N.B. We make the recursion in the first argument.
postulate
  S₅ : ∀ n →   zero   + n ≣ n
  S₆ : ∀ m n → succ m + n ≣ succ (m + n)
{-# ATP axiom S₅ #-}
{-# ATP axiom S₆ #-}

-- N.B. We make the recursion on the first argument.
postulate
  S₇ : ∀ n →   zero   * n ≣ zero
  S₈ : ∀ m n → succ m * n ≣ n + m * n
{-# ATP axiom S₇ #-}
{-# ATP axiom S₈ #-}

postulate
  -- The axiom S₉ is a higher-order one, therefore we do not translate it
  -- as an ATP axiom.
  S₉ : (P : ℕ → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
