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
-- From (Machover 1996, p. 263) and (Hájek and Pudlák 1998, p. 28):
--
-- PA₁. 0 ≠ n'
-- PA₂. m' = n' → m = n
-- PA₃. 0 + n = n
-- PA₄. m' + n = (m + n)'
-- PA₅. 0 * n = 0
-- PA₆. m' * n = n + (m * n)
-- Axiom of induction:
-- φ(0) → (∀n.φ(n) → φ(succ n)) → ∀n.φ(n), for any formulae φ

-- References:
--
-- • Moshé Machover. Set theory, logic and their
--   limitations. Cambridge University Press, 1996.
--
-- • Petr Hájek and Pavel Pudlák. Metamathematics of First-Order
--   Arithmetic. Springer, 1998. 2nd printing.

postulate
  PA₁ : ∀ {n} → zero ≢ succ n
  PA₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
  PA₃ : ∀ n → zero + n ≡ n
  PA₄ : ∀ m n → succ m + n ≡ succ (m + n)
  PA₅ : ∀ n → zero * n ≡ zero
  PA₆ : ∀ m n → succ m * n ≡ n + m * n
{-# ATP axiom PA₁ PA₂ PA₃ PA₄ PA₅ PA₆ #-}

-- The axiom of induction is an axiom schema, therefore we do not
-- translate it to TPTP.
postulate
  PA-ind : (A : M → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
