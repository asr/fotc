module Test.Succeed.LocalHints where

postulate
  D    : Set
  zero : D

data N : D → Set where
  zN : N zero

postulate foo : N zero
{-# ATP prove foo zN #-}
