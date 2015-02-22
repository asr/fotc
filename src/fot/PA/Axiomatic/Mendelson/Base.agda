------------------------------------------------------------------------------
-- Axiomatic Peano arithmetic base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Mendelson's axioms for first-order Peano arithmetic [Mendelson,
-- 1977, p. 155].

-- Elliott Mendelson. Introduction to mathematical logic. Chapman &
-- Hall, 4th edition, 1997, p. 155.

-- NB. These axioms formalize the propositional equality.

module PA.Axiomatic.Mendelson.Base where

infixl 7 _*_
infixl 6 _+_
infix  4 _≈_ _≉_

------------------------------------------------------------------------------
-- First-order logic (without equality)
open import Common.FOL.FOL public renaming ( D to ℕ )

-- Non-logical constants
postulate
  zero    : ℕ
  succ    : ℕ → ℕ
  _+_ _*_ : ℕ → ℕ → ℕ

-- The PA equality.
--
-- N.B. The symbol _≡_ should not be used because it is hard-coded by
-- Apia as the ATPs equality.
postulate _≈_ : ℕ → ℕ → Set

-- Inequality.
_≉_ : ℕ → ℕ → Set
x ≉ y = ¬ x ≈ y
{-# ATP definition _≉_ #-}

-- Proper axioms

-- S₁. m = n → m = o → n = o
-- S₂. m = n → succ m = succ n
-- S₃. 0 ≠ succ n
-- S₄. succ m = succ n → m = n
-- S₅. 0 + n = n
-- S₆. succ m + n = succ (m + n)
-- S₇. 0 * n = 0
-- S₈. succ m * n = (m * n) + n
-- S₉. P(0) → (∀n.P(n) → P(succ n)) → ∀n.P(n), for any wff P(n) of PA.

postulate
  S₁ : ∀ {m n o} → m ≈ n → m ≈ o → n ≈ o
  S₂ : ∀ {m n} → m ≈ n → succ m ≈ succ n
  S₃ : ∀ {n} → zero ≉ succ n
  S₄ : ∀ {m n} → succ m ≈ succ n → m ≈ n
  S₅ : ∀ n → zero + n ≈ n
  S₆ : ∀ m n → succ m + n ≈ succ (m + n)
  S₇ : ∀ n → zero * n ≈ zero
  S₈ : ∀ m n → succ m * n ≈ n + m * n
{-# ATP axiom S₁ S₂ S₃ S₄ S₅ S₆ S₇ S₈ #-}

-- S₉ is an axiom schema, therefore we do not translate it to TPTP.
postulate S₉ : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
