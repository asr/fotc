------------------------------------------------------------------------------
-- Conversion functions i, j and k.
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.IJK where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

-- Conversion functions from/to ℕ and N.
i : ℕ → D
i z     = zero
i (s n) = succ₁ (i n)

j : (n : ℕ) → N (i n)
j z     = nzero
j (s n) = nsucc (j n)

k : {n : D} → N n → ℕ
k nzero      = z
k (nsucc Nn) = s (k Nn)

_+_ : ℕ → ℕ → ℕ
z   + n = n
s m + n = s (m + n)
