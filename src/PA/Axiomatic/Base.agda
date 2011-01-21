------------------------------------------------------------------------------
-- Axiomatic Peano arithmetic base
------------------------------------------------------------------------------

module PA.Axiomatic.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infix  7  _≣_
infixl 9  _+_

------------------------------------------------------------------------------
-- PA universe
open import Common.Universe public renaming ( D to ℕ )

-- Logical constants
open import Common.LogicalConstants public

-- Non-logical constants
postulate
  zero : ℕ
  succ : ℕ → ℕ
  _+_  : ℕ → ℕ → ℕ
  _*_  : ℕ → ℕ → ℕ

-- The PA equality.
-- N.B. The symbol _≡_ should not be used because it is hard-coded by
-- the tool agda2atp as the ATPs equality.
postulate
  _≣_ : ℕ → ℕ → Set

-- Proper axioms
-- (From Elliott Mendelson. Introduction to mathematical
-- logic. Chapman & Hall, 4th edition, 1997, p. 155)

-- N.B. We make the recursion in the first argument for _+_ and _*_.

-- S₁. m = n → m = o → n = o
-- S₂. m = n → succ m = succ n
-- S₃. 0 ≠ succ n
-- S₄. succ m = succ n → m = n
-- S₅. 0 + n = n
-- S₆. succ m + n = succ (m + n)
-- S₇. 0 * n = 0
-- S₈. succ m * n = (m * n) + m
-- S₉. P(0) → (∀n.P(n) → P(succ n)) → ∀n.P(n), for any wf P(n) of PA.

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

postulate
  S₅ : ∀ n →   zero   + n ≣ n
  S₆ : ∀ m n → succ m + n ≣ succ (m + n)
{-# ATP axiom S₅ #-}
{-# ATP axiom S₆ #-}

postulate
  S₇ : ∀ n →   zero   * n ≣ zero
  S₈ : ∀ m n → succ m * n ≣ n + m * n
{-# ATP axiom S₇ #-}
{-# ATP axiom S₈ #-}

postulate
  -- The axiom S₉ is a higher-order one, therefore we do not translate it
  -- as an ATP axiom.
  S₉ : (P : ℕ → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
