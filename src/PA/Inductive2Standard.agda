------------------------------------------------------------------------------
-- From inductive PA to axiomatic PA (using the standard
-- propositional equality)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the definition of PA using Agda data types and primitive
-- recursive functions for addition and multiplication, we can prove the
-- following axioms (see [p. 263, 1], [p. 28, 2]):

-- N.B. We make the recursion in the first argument for _+_ and _*_.

-- A₁. 0 ≠ succ n
-- A₂. succ m = succ n → m = n
-- A₃. 0 + n = n
-- A₄. succ m + n = succ (m + n)
-- A₅. 0 * n = 0
-- A₆. succ m * n = (m * n) + m
-- A₇. P(0) → (∀n.P(n) → P(succ n)) → ∀n.P(n), for any wff P(n) of PA.

-- [1] Moshé Machover. Set theory, logic and their
-- limitations. Cambridge University Press, 1996.

-- [2] Petr Hájeck and Pavel Pudlák. Metamathematics of First-Order
--     Arithmetic. Springer, 1998. 2nd printing.

module PA.Inductive2Standard where

open import FOL.Relation.Nullary

open import PA.Inductive.Base

------------------------------------------------------------------------------

A₁ : ∀ {n} → ¬ (zero ≡ succ n)
A₁ ()

A₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
A₂ refl = refl

A₃ : ∀ n → zero + n ≡ n
A₃ n = refl

A₄ : ∀ m n → succ m + n ≡ succ (m + n)
A₄ m n = refl

A₅ : ∀ n → zero * n ≡ zero
A₅ n = refl

A₆ : ∀ m n → succ m * n ≡ n + m * n
A₆ m n = refl

A₇ : (P : M → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
A₇ P P0 h zero     = P0
A₇ P P0 h (succ n) = h n (A₇ P P0 h n)
