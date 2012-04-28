------------------------------------------------------------------------------
-- From inductive PA to axiomatic PA (using the standard
-- propositional equality)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the definition of PA using Agda data types and primitive
-- recursive functions for addition and multiplication, we can prove
-- the following axioms (see (Machover 1996, p. 263) and (Hájek and
-- Pudlák 1998, p. 28)):

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

-- • Petr Hájek and Pavel Pudlák. Metamathematics of First-Order
--   Arithmetic. Springer, 1998. 2nd printing.

module PA.Inductive2Standard where

open import PA.Inductive.Base

------------------------------------------------------------------------------

PA₁ : ∀ {n} → ¬ (zero ≡ succ n)
PA₁ ()

PA₂ : ∀ {m n} → succ m ≡ succ n → m ≡ n
PA₂ refl = refl

PA₃ : ∀ n → zero + n ≡ n
PA₃ n = refl

PA₄ : ∀ m n → succ m + n ≡ succ (m + n)
PA₄ m n = refl

PA₅ : ∀ n → zero * n ≡ zero
PA₅ n = refl

PA₆ : ∀ m n → succ m * n ≡ n + m * n
PA₆ m n = refl
