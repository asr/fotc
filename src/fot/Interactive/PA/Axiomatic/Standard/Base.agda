------------------------------------------------------------------------------
-- Axiomatic Peano arithmetic base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.PA.Axiomatic.Standard.Base where

infixl 7 _*_
infixl 6 _+_

------------------------------------------------------------------------------
-- First-order logic with equality.
open import Common.FOL.FOL-Eq public renaming ( D to ℕ )

-- Common definitions.
open import Interactive.Common.Definitions

-- Non-logical constants
postulate
  zero    : ℕ
  succ    : ℕ → ℕ
  _+_ _*_ : ℕ → ℕ → ℕ

-- Proper axioms
-- From [Machover 1996, p. 263] and [Hájek and Pudlák 1998, p. 28]:
--
-- PA₁. 0 ≠ n'
-- PA₂. m' = n' → m = n
-- PA₃. 0 + n = n
-- PA₄. m' + n = (m + n)'
-- PA₅. 0 * n = 0
-- PA₆. m' * n = n + (m * n)
-- Axiom of induction:
-- φ(0) → (∀n.φ(n) → φ(succ n)) → ∀n.φ(n), for any formulae φ

postulate
  PA₁ : ∀ {n} → zero ≢ succ n
  PA₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
  PA₃ : ∀ n → zero + n ≡ n
  PA₄ : ∀ m n → succ m + n ≡ succ (m + n)
  PA₅ : ∀ n → zero * n ≡ zero
  PA₆ : ∀ m n → succ m * n ≡ n + m * n

postulate
  ℕ-ind : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n

------------------------------------------------------------------------------
-- References
--
-- Machover, Moshé (1996). Set theory, Logic and their
-- Limitations. Cambridge University Press.

-- Hájek, Petr and Pudlák, Pavel (1998). Metamathematics of
-- First-Order Arithmetic. 2nd printing. Springer.
