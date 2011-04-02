module Pure where

postulate
  D    : Set
  zero : D
  succ : D → D
  N    : D → Set

postulate
  zN : N zero
  sN : ∀ {n} → N n → N (succ n)
{-# ATP axiom zN #-}
{-# ATP axiom sN #-}
