------------------------------------------------------------------------------
-- The PA natural numbers type
------------------------------------------------------------------------------

module Draft.PA.Type where

open import Draft.PA.Base

------------------------------------------------------------------------------
-- The inductive predicate 'N' represents the type of the natural
-- numbers. They are a subset of 'PA'.

-- The PA natural numbers type.
data N : PA → Set where
  zN : N zero
  sN : {n : PA} → N n → N (succ n)
-- {-# ATP hint zN #-}
-- {-# ATP hint sN #-}

-- Induction principle for N (elimination rule).
indN : (P : PA → Set) →
       P zero →
       ({n : PA} → N n → P n → P (succ n)) →
       {n : PA} → N n → P n
indN P p0 h zN      = p0
indN P p0 h (sN Nn) = h Nn (indN P p0 h Nn)
