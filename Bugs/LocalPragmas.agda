-- See descripion in Bugs.LocalPragmas.OtherModule

module Bugs.LocalPragmas where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)
-- {-# ATP axiom zN #-}
