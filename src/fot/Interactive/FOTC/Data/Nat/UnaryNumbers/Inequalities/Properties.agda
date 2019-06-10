------------------------------------------------------------------------------
-- Properties of the inequalities of unary numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Nat.UnaryNumbers.Inequalities.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.Properties
open import Interactive.FOTC.Data.Nat.Properties
open import Interactive.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

-- TODO (2019-06-09): Missing proof.
postulate x<x+1 : ∀ {n} → N n → n < n + 1'

-- TODO (2019-06-09): Missing proof.
postulate x<x+11 : ∀ {n} → N n → n < n + 11'
