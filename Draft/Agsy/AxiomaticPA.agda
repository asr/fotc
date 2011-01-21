------------------------------------------------------------------------------
-- Axiomatic Peano arithmetic using Agsy
------------------------------------------------------------------------------

module AxiomaticPA where

open import Common.Relation.Nullary

infixl 10 _*_
infix  7  _≣_
infixl 9  _+_

------------------------------------------------------------------------------
-- PA universe
open import Common.Universe public renaming ( D to ℕ )

-- Non-logical constants
postulate
  zero : ℕ
  succ : ℕ → ℕ
  _+_  : ℕ → ℕ → ℕ
  _*_  : ℕ → ℕ → ℕ
  _≣_  : ℕ → ℕ → Set

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
  S₁ : {m n o : ℕ} → m ≣ n → m ≣ o → n ≣ o
  S₂ : ∀ {m n} → m ≣ n → succ m ≣ succ n
  S₃ : ∀ {n} → ¬ (zero ≣ succ n)
  S₄ : ∀ {m n} → succ m ≣ succ n → m ≣ n
  S₅ : ∀ n →   zero   + n ≣ n
  S₆ : ∀ m n → succ m + n ≣ succ (m + n)
  S₇ : ∀ n →   zero   * n ≣ zero
  S₈ : ∀ m n → succ m * n ≣ n + m * n
  S₉ : (P : ℕ → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n

-- Properties

refl : ∀ {n} → n ≣ n
refl {n} = S₁ (S₅ n) (S₅ n) -- Via Agsy {-m}

sym : ∀ {m n} → m ≣ n → n ≣ m
sym m≣n = S₁ m≣n refl  -- Via Agsy {-m}

trans : ∀ {m n o} → m ≣ n → n ≣ o → m ≣ o
trans m≣n n≣o = S₁ (sym m≣n) n≣o  -- Via Agsy {-m}

+-rightIdentity : ∀ n → n + zero ≣ n
+-rightIdentity n = {!-t 20 -m!}  -- Agsy fails
