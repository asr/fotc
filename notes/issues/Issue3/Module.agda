{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 19 July 2012.

-- See descripion in Issue3.OtherModule

module Issue3.Module where

postulate
  D    : Set
  _≡_  : D → D → Set
  a b  : D

postulate p : a ≡ b
-- {-# ATP axiom p #-}
