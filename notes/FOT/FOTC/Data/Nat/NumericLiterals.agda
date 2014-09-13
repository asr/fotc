------------------------------------------------------------------------------
-- Testing the use of numeric literals
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Nat.NumericLiterals where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

toD : ℕ → D
toD z     = zero
toD (s n) = succ₁ (toD n)

ten : D
ten = toD 10
