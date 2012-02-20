------------------------------------------------------------------------------
-- The LTC-PCF natural numbers type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Type where

open import LTC-PCF.Base

------------------------------------------------------------------------------
-- The inductive predicate 'N' represents the type of the natural
-- numbers. They are a subset of 'D'.

-- The LTC-PCF natural numbers type.
data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ₁ n)
{-# ATP axiom zN sN #-}

-- Induction principle for N (elimination rule).
N-ind : (P : D → Set) →
       P zero →
       (∀ {n} → P n → P (succ₁ n)) →
       ∀ {n} → N n → P n
N-ind P P0 h zN      = P0
N-ind P P0 h (sN Nn) = h (N-ind P P0 h Nn)
