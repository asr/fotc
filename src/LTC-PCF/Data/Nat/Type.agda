------------------------------------------------------------------------------
-- The LTC-PCF natural numbers type
------------------------------------------------------------------------------

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
indN : (P : D → Set) →
       P zero →
       (∀ {n} → P n → P (succ₁ n)) →
       ∀ {n} → N n → P n
indN P P0 h zN      = P0
indN P P0 h (sN Nn) = h (indN P P0 h Nn)
