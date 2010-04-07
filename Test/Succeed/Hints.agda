------------------------------------------------------------------------------
-- Testing the use of general hints
------------------------------------------------------------------------------

module Test.Succeed.Hints where

postulate
  D    : Set
  zero : D

data N : D → Set where
  zN : N zero
-- A general hint
{-# ATP hint zN #-}

postulate
  p₁ : N zero
{-# ATP prove p₁ #-}
