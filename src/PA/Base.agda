------------------------------------------------------------------------------
-- Peano arithmetic base
------------------------------------------------------------------------------

module PA.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_
infix  7 _≡_

------------------------------------------------------------------------------
-- PA universe.
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- The identity type on ℕ
data _≡_ (n : ℕ) : ℕ → Set where
  refl : n ≡ n

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero   * n = zero
succ m * n = n + m * n
