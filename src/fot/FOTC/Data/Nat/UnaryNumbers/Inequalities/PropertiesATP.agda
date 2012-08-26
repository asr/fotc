------------------------------------------------------------------------------
-- Properties of the inequalities of unary numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate x<x+1 : ∀ {n} → N n → LT n (n + one)
{-# ATP prove x<x+1 x<Sx +-comm #-}

postulate x<x+11 : ∀ {n} → N n → LT n (n + eleven)
{-# ATP prove x<x+11 x<x+Sy #-}
