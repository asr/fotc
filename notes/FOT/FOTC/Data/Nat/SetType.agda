------------------------------------------------------------------------------
-- Testing a type synonymous for Set
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Nat.SetType where

open import FOTC.Base
open import FOTC.Data.Nat

-- Type synonymous for Set.
Type = Set

data N' : D → Type where
  nzero' : N' zero
  nsucc' : ∀ {n} → N' n → N' (succ₁ n)
{-# ATP axiom nzero' nsucc' #-}

pred-N' : ∀ {n} → N' n → N' (pred₁ n)
pred-N' nzero' = prf
  where postulate prf : N' (pred₁ zero)
        {-# ATP prove prf #-}

pred-N' (nsucc' {n} N'n) = prf
  where postulate prf : N' (pred₁ (succ₁ n))
        {-# ATP prove prf #-}
