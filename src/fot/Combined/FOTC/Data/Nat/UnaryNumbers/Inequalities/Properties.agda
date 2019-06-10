------------------------------------------------------------------------------
-- Properties of the inequalities of unary numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat.UnaryNumbers.Inequalities.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.Properties
open import Combined.FOTC.Data.Nat.Properties
open import Combined.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate x<x+1 : ∀ {n} → N n → n < n + 1'
{-# ATP prove x<x+1 x<Sx +-comm #-}

postulate x<x+11 : ∀ {n} → N n → n < n + 11'
{-# ATP prove x<x+11 x<x+Sy #-}
