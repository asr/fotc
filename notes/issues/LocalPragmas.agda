{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 12 July 2012.

-- See descripion in LocalPragmas.OtherModule

module LocalPragmas where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)
-- {-# ATP axiom zN #-}
