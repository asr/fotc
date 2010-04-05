------------------------------------------------------------------------------
-- Testing the use of general hints
------------------------------------------------------------------------------

module Test.Succeed.Hints where

infix  4 _≡_

postulate
  D      : Set
  zero   : D
  succ   : D → D
  pred   : D → D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN : {n : D} → N n → N (succ n)

-- A general hint
{-# ATP hint zN #-}

-- A conversion rule for pred.
postulate
  cP₁ : pred zero ≡ zero
{-# ATP axiom cP₁ #-}

-- This postulate requires the hint zN for its proof by the ATP.
postulate
  pred-N-prf₁ : N (pred zero)
{-# ATP prove pred-N-prf₁ #-}
