------------------------------------------------------------------------------
-- Inductive PA properties commons to the interactive and automatic proofs
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.Properties where

open import FOL.Relation.Nullary
open import PA.Inductive.Base

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

-- Peano's third axiom.
P₃ : ∀ {m n} → succ m ≡ succ n → m ≡ n
P₃ refl = refl

-- Peano's fourth axiom.
P₄ : ∀ {n} → ¬ (zero ≡ succ n)
P₄ ()

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = cong succ (+-rightIdentity n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero     _ _ = refl
+-assoc (succ m) n o = cong succ (+-assoc m n o)

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] zero     _ = refl
x+Sy≡S[x+y] (succ m) n = cong succ (x+Sy≡S[x+y] m n)
