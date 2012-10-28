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
m + n = rec m n (lam (λ _ → lam succ₁))

∸-helper : D → D
∸-helper f = lam (λ m → lam (λ n →
               if (iszero₁ n)
                  then m
                  else if (iszero₁ m)
                          then zero
                          else f · pred₁ m · pred₁ n))

-- See note [Subtraction with the rec combinator].
_∸_ : D → D → D
_∸_ m n = fix ∸-helper · m · n

-- Multiplication with recursion on the first argument.
_*_ : D → D → D
m * n = rec m zero (lam (λ _ → lam (λ x → n + x)))

------------------------------------------------------------------------------
-- Note [Subtraction with the rec combinator (27 October 2012)].
-- Using the rec combinator for defining subtraction
--
-- _∸_ : D → D → D
-- m ∸ n = rec n m (lam (λ _ → lam pred₁))
--
-- we could not prove the conversion rules without using total natural
-- numbers hypotheses (see
-- FOT.LTC-PCF.Data.Nat.SubtractionRecCombinator in the directory
-- notes).
