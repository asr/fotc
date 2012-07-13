------------------------------------------------------------------------------
-- Testing Agda internal terms: Con
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The following hint uses the internal Agda term @Con@.

module AgdaInternalTerms.ConTerm where

-- We add 3 to the fixities of the standard library.
infixl 9 _+_
infix  7 _≡_

------------------------------------------------------------------------------

data ℕ : Set where
  zero :     ℕ
  succ : ℕ → ℕ

data _≡_ (n : ℕ) : ℕ → Set where
  refl : n ≡ n

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

+-0x : ∀ n → zero + n ≡ n
+-0x n = refl
{-# ATP hint +-0x #-}

postulate foo : ∀ n → zero + n ≡ n
{-# ATP prove foo #-}
