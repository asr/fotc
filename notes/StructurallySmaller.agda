module StructurallySmaller where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

-- Foo is not structurally recursive even though zero + n normalises
-- to n.
{-# NO_TERMINATION_CHECK #-}
foo : ℕ → ℕ
foo zero     = zero
foo (succ n) = foo (zero + n)
