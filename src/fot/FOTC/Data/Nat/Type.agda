------------------------------------------------------------------------------
-- The FOTC natural numbers type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Nat.

module FOTC.Data.Nat.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC natural numbers type (inductive predicate for the total
-- natural numbers).
data N : D → Set where
  nzero :               N zero
  nsucc : ∀ {n} → N n → N (succ₁ n)
{-# ATP axiom nzero nsucc #-}

-- Induction principle.
N-ind : (A : D → Set) →
       A zero →
       (∀ {n} → A n → A (succ₁ n)) →
       ∀ {n} → N n → A n
N-ind A A0 h nzero      = A0
N-ind A A0 h (nsucc Nn) = h (N-ind A A0 h Nn)
