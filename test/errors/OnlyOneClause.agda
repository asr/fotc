------------------------------------------------------------------------------
-- We only translate definition with one clause
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module OnlyOneClause where

infix 7 _≡_

data ℕ : Set where
  zero :     ℕ
  succ : ℕ → ℕ

data _≡_ (n : ℕ) : ℕ → Set where
  refl : n ≡ n

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)
{-# ATP definition _+_ #-}

postulate +-comm : ∀ m n → m + n ≡ n + m
{-# ATP prove +-comm #-}
