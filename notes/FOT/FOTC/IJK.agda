------------------------------------------------------------------------------
-- Conversion functions i, j, and k.
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.IJK where

open import FOTC.Base
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

-- The inductive natural numbers.
data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

-- Conversion functions
i : ℕ → D
i z     = zero
i (s n) = succ₁ (i n)

j : (n : ℕ) → N (i n)
j z     = nzero
j (s n) = nsucc (j n)

k : {n : D} → N n → ℕ
k nzero      = z
k (nsucc Nn) = s (k Nn)

-- Addition for ℕ
_+_ : ℕ → ℕ → ℕ
z   + n = n
s m + n = s (m + n)
