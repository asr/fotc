{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 19 July 2012.

module Issue3a where

module A where
  postulate
    D    : Set
    _≡_  : D → D → Set
    a b  : D

  postulate p : a ≡ b

open A
{-# ATP axiom p #-}

-- It works!
postulate foo : a ≡ b
{-# ATP prove foo #-}
