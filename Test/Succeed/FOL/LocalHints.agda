------------------------------------------------------------------------------
-- Testing the use local hints
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.LocalHints where

postulate
  D    : Set
  zero : D

data N : D → Set where
  zN : N zero

postulate 0-N : N zero
{-# ATP prove 0-N zN #-}
