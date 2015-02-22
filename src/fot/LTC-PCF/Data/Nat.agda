------------------------------------------------------------------------------
-- Natural numbers (PCF version)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Type public

infixl 7 _*_
infixl 6 _+_ _∸_

------------------------------------------------------------------------------
-- Addition with recursion on the first argument.
_+_ : D → D → D
m + n = rec m n (lam (λ _ → lam succ₁))

-- Subtraction with recursion on the second argument.
_∸_ : D → D → D
m ∸ n = rec n m (lam (λ _ → lam pred₁))

-- Multiplication with recursion on the first argument.
_*_ : D → D → D
m * n = rec m zero (lam (λ _ → lam (λ x → n + x)))
