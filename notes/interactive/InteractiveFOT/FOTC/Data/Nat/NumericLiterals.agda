------------------------------------------------------------------------------
-- Testing the use of numeric literals
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Data.Nat.NumericLiterals where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat

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
