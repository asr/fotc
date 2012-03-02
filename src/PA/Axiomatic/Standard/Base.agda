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
-- FOL with equality.
--
-- We chose the symbol M because there are non-standard models of
-- Peano Arithmetic, where the domain is not the set of natural
-- numbers.
open import Common.FOL.FOL-Eq public renaming ( D to M )

-- Non-logical constants
postulate
  zero    : M
  succ    : M → M
  _+_ _*_ : M → M → M

-- Proper axioms
-- From [Machover, 1996, p. 263] and [Hájek and Pudlák, 1998, p. 28]:
--
-- * Moshé Machover. Set theory, logic and their
--   limitations. Cambridge University Press, 1996.
--
-- * Petr Hájek and Pavel Pudlák. Metamathematics of First-Order
--   Arithmetic. Springer, 1998. 2nd printing.

-- A₁. 0 ≠ n'
-- A₂. m' = n' → m = n
-- A₃. 0 + n = n
-- A₄. m' + n = (m + n)'
-- A₅. 0 * n = 0
-- A₆. m' * n = n + (m * n)
-- Axiom of induction:
-- φ(0) → (∀n.φ(n) → φ(succ n)) → ∀n.φ(n), for any formulae φ

postulate
  A₁ : ∀ {n} → ¬ (zero ≡ succ n)
  A₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
  A₃ : ∀ n → zero + n ≡ n
  A₄ : ∀ m n → succ m + n ≡ succ (m + n)
  A₅ : ∀ n → zero * n ≡ zero
  A₆ : ∀ m n → succ m * n ≡ n + m * n
{-# ATP axiom A₁ A₂ A₃ A₄ A₅ A₆ #-}

-- The axiom of induction is an axiom schema, therefore we do not
-- translate it to TPTP.
postulate
  PA-ind : (A : M → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
