------------------------------------------------------------------------------
-- From inductive PA to axiomatic PA (using the standard
-- propositional equality)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the definition of PA using Agda data types and primitive
-- recursive functions for addition and multiplication, we can prove
-- the following axioms (see [Machover, 1996, p. 263], [Hájek and
-- Pudlák, 1998, p. 28]):

-- A₁. 0 ≠ n'
-- A₂. m' = n' → m = n
-- A₃. 0 + n = n
-- A₄. m' + n = (m + n)'
-- A₅. 0 * n = 0
-- A₆. m' * n = n + (m * n)
-- Axiom of induction:
-- φ(0) → (∀n.φ(n) → φ(succ n)) → ∀n.φ(n), for any formulae φ

-- [1] Moshé Machover. Set theory, logic and their
-- limitations. Cambridge University Press, 1996.

-- [2] Petr Hájek and Pavel Pudlák. Metamathematics of First-Order
--     Arithmetic. Springer, 1998. 2nd printing.

module PA.Inductive2Standard where

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
