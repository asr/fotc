------------------------------------------------------------------------------
-- Inductive PA properties commons to the interactive and automatic proofs
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.Properties where

open import FOL.Relation.Nullary
open import PA.Inductive.Base

------------------------------------------------------------------------------
-- Congruence properties

succ-cong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succ-cong = cong succ

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong h = cong₂ _+_ h refl

-- TODO: It is strictly necessary the implicit argument m?
+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong {m} h = cong₂ _+_ {m} refl h

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

-- Adapted from the Agda standard library v0.6 (see
-- Data.Nat.Properties.n+0≡n).
+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = succ-cong (+-rightIdentity n)

-- Adapted from the Agda standard library v0.6 (see
-- Data.Nat.Properties.+-assoc).
+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero     _ _ = refl
+-assoc (succ m) n o = succ-cong (+-assoc m n o)

-- Adapted from the Agda standard library v0.6 (see
-- Data.Nat.Properties.m+1+n≡1+m+n).
x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] zero     _ = refl
x+Sy≡S[x+y] (succ m) n = succ-cong (x+Sy≡S[x+y] m n)
