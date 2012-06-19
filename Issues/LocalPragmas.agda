{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- See descripion in Issues.LocalPragmas.OtherModule

module Issues.LocalPragmas where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)
-- {-# ATP axiom zN #-}
