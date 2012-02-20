------------------------------------------------------------------------------
-- Axiomatic Peano arithmetic base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Standard.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_

------------------------------------------------------------------------------
-- PA universe.
-- We chose the symbol M because there are non-standard models of
-- Peano Arithmetic, where the domain is not the set of natural
-- numbers.
open import Common.Universe public renaming ( D to M )

-- The PA equality
-- The PA equality is the propositional identity on the universal domain.
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.Inductive public

-- Logical constants
open import Common.LogicalConstants public

-- Non-logical constants
postulate
  zero    : M
  succ    : M → M
  _+_ _*_ : M → M → M

-- Proper axioms (see [p. 263, 1], [p. 28, 2])
--
-- [1] Moshé Machover. Set theory, logic and their
--     limitations. Cambridge University Press, 1996.
--
-- [2] Petr Hájeck and Pavel Pudlák. Metamathematics of First-Order
--     Arithmetic. Springer, 1998. 2nd printing.

-- A₁. 0 ≠ succ n
-- A₂. succ m = succ n → m = n
-- A₃. 0 + n = n
-- A₄. succ m + n = succ (m + n)
-- A₅. 0 * n = 0
-- A₆. succ m * n = (m * n) + m
-- A₇. P(0) → (∀n.P(n) → P(succ n)) → ∀n.P(n), for any wff P(n) of PA.

postulate
  A₁ : ∀ {n} → ¬ (zero ≡ succ n)
  A₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
  A₃ : ∀ n → zero + n ≡ n
  A₄ : ∀ m n → succ m + n ≡ succ (m + n)
  A₅ : ∀ n → zero * n ≡ zero
  A₆ : ∀ m n → succ m * n ≡ n + m * n
{-# ATP axiom A₁ A₂ A₃ A₄ A₅ A₆ #-}

-- A₇ is an axiom schema, therefore we do not translate it to TPTP.
postulate A₇ : (P : M → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
