------------------------------------------------------------------------------
-- From inductive PA to Mendelson's axioms for PA
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the definition of PA using Agda data types and primitive
-- recursive functions for addition and multiplication, we can prove the
-- Mendelson's axioms [1].

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

-- [1]. Elliott Mendelson. Introduction to mathematical
--      logic. Chapman& Hall, 4th edition, 1997, p. 155.

module PA.Inductive2Mendelson where

open import FOL.Relation.Nullary

open import PA.Inductive.Base

------------------------------------------------------------------------------

S₁ :  ∀ {m n o} → m ≡ n → m ≡ o → n ≡ o
S₁ refl refl = refl

S₂ : ∀ {m n} → m ≡ n → succ m ≡ succ n
S₂ refl = refl

S₃ : ∀ {n} → ¬ (zero ≡ succ n)
S₃ ()

S₄ : ∀ {m n} → succ m ≡ succ n → m ≡ n
S₄ refl = refl

S₅ : ∀ n → zero + n ≡ n
S₅ n = refl

S₆ : ∀ m n → succ m + n ≡ succ (m + n)
S₆ m n = refl

S₇ : ∀ n → zero * n ≡ zero
S₇ n = refl

S₈ : ∀ m n → succ m * n ≡ n + m * n
S₈ m n = refl

S₉ : (P : M → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
S₉ = PA-ind
