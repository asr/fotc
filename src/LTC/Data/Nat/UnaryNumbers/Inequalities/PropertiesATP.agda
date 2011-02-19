------------------------------------------------------------------------------
-- Properties of the inequalities of unary numbers
------------------------------------------------------------------------------

module LTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP where

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate
  x<x+1 : ∀ {n} → N n → LT n (n + one)
{-# ATP prove x<x+1 x<Sx +-comm #-}

postulate
  x<x+11 : ∀ {n} → N n → LT n (n + eleven)
{-# ATP prove x<x+11 x<x+Sy #-}
