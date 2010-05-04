------------------------------------------------------------------------------
-- Inductive predicate for the total natural numbers
------------------------------------------------------------------------------

module LTC.Data.N where

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

-- Pairs of LTC natural numbers.
-- Used by the lexicographical induction on N.
data N₂ : D × D → Set where
  _,_ : {m n : D} → N m → N n → N₂ (m , n)

N₂-proj₁ : {mn : D × D} → N₂ mn → N (×-proj₁ mn)
N₂-proj₁ (Nm , _) = Nm

N₂-proj₂ : {mn : D × D} → N₂ mn → N (×-proj₂ mn)
N₂-proj₂ (_ , Nn) = Nn
