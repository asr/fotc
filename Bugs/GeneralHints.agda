module Bugs.GeneralHints where

postulate
  D    : Set
  _≡_  : D → D → Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)
