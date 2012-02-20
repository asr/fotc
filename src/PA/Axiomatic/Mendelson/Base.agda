------------------------------------------------------------------------------
-- Axiomatic Peano arithmetic base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Mendelson's axioms for first-order Peano arithmetic [1].
-- NB. These axioms formalize the propositional equality.

-- [1] Elliott Mendelson. Introduction to mathematical logic. Chapman &
--     Hall, 4th edition, 1997, p. 155.

module PA.Axiomatic.Mendelson.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_
infix  7  _≐_

------------------------------------------------------------------------------
-- PA universe.
-- We chose the symbol M because there are non-standard models of
-- Peano Arithmetic, where the domain is not the set of natural
-- numbers.
open import Common.Universe public renaming ( D to M )

-- Logical constants
open import Common.LogicalConstants public

-- Non-logical constants
postulate
  zero    : M
  succ    : M → M
  _+_ _*_ : M → M → M

-- The PA equality.
-- N.B. The symbol _≡_ should not be used because it is hard-coded by
-- the program agda2atp as the ATPs equality.
postulate _≐_ : M → M → Set

-- Proper axioms

-- S₁. m = n → m = o → n = o
-- S₂. m = n → succ m = succ n
-- S₃. 0 ≠ succ n
-- S₄. succ m = succ n → m = n
-- S₅. 0 + n = n
-- S₆. succ m + n = succ (m + n)
-- S₇. 0 * n = 0
-- S₈. succ m * n = (m * n) + m
-- S₉. P(0) → (∀n.P(n) → P(succ n)) → ∀n.P(n), for any wff P(n) of PA.

postulate
  S₁ : ∀ {m n o} → m ≐ n → m ≐ o → n ≐ o
  S₂ : ∀ {m n} → m ≐ n → succ m ≐ succ n
  S₃ : ∀ {n} → ¬ (zero ≐ succ n)
  S₄ : ∀ {m n} → succ m ≐ succ n → m ≐ n
  S₅ : ∀ n → zero + n ≐ n
  S₆ : ∀ m n → succ m + n ≐ succ (m + n)
  S₇ : ∀ n → zero * n ≐ zero
  S₈ : ∀ m n → succ m * n ≐ n + m * n
{-# ATP axiom S₁ S₂ S₃ S₄ S₅ S₆ S₇ S₈ #-}

-- S₉ is an axiom schema, therefore we do not translate it to TPTP.
postulate S₉ : (P : M → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
