------------------------------------------------------------------------------
-- Testing Agda internal terms: Con
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The following hint uses the internal Agda term @Con@.

module Test.Succeed.FOL.AgdaInternalTerms.ConTerm where

-- We add 3 to the fixities of the standard library.
infixl 9 _+_
infix  7 _≡_

------------------------------------------------------------------------------

data M : Set where
  zero :     M
  succ : M → M

data _≡_ (m : M) : M → Set where
  refl : m ≡ m

_+_ : M → M → M
zero   + n = n
succ m + n = succ (m + n)

+-0x : ∀ n → zero + n ≡ n
+-0x n = refl
{-# ATP hint +-0x #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate foo : ∀ n → n ≡ n
{-# ATP prove foo #-}
