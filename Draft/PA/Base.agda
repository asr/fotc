------------------------------------------------------------------------------
-- Peano arithmetic base
------------------------------------------------------------------------------

module Draft.PA.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_
infix  7 _≡_

------------------------------------------------------------------------------
-- PA universe

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- The identity type on ℕ
data _≡_ (n : ℕ) : ℕ → Set where
  refl : n ≡ n

-- Non-logical constants
postulate
  _+_  : ℕ → ℕ → ℕ
  _*_  : ℕ → ℕ → ℕ

postulate
  S₅  : ∀ n →   zero   + n ≡ n
  S₆  : ∀ m n → succ m + n ≡ succ (m + n)
  S₇ : ∀ n →   zero   * n ≡ zero
  S₈ : ∀ m n → succ m * n ≡ m + n * m

{-# ATP axiom S₅ #-}
{-# ATP axiom S₆ #-}
{-# ATP axiom S₇ #-}
{-# ATP axiom S₈ #-}
