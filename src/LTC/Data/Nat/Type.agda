------------------------------------------------------------------------------
-- The LTC natural numbers type
------------------------------------------------------------------------------

module LTC.Data.Nat.Type where

open import LTC.Minimal

------------------------------------------------------------------------------
-- The inductive predicate 'N' represents the type of the natural
-- numbers. They are a subset of 'D'.

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN : {n : D} → N n → N (succ n)
-- {-# ATP hint zN #-}
-- {-# ATP hint sN #-}

-- Induction principle for N (elimination rule).
indN : (P : D → Set) →
       P zero →
       ({n : D} → N n → P n → P (succ n)) →
       {n : D} → N n → P n
indN P p0 h zN      = p0
indN P p0 h (sN Nn) = h Nn (indN P p0 h Nn)
