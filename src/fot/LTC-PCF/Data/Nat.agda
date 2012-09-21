------------------------------------------------------------------------------
-- Natural numbers (PCF version)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_ _∸_

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Type public

------------------------------------------------------------------------------
-- Addition with recursion on the first argument.
_+_ : D → D → D
m + n = rec m n (lam (λ x → lam (λ y → succ₁ y)))

_∸_ : D → D → D
m ∸ n = rec n m (lam (λ x → lam (λ y → pred₁ y)))

-- Multiplication with recursion on the first argument.
_*_ : D → D → D
m * n = rec m zero (lam (λ _ → lam (λ y → n + y)))
