{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with agda2atp on 19 July 2012.

module Modules2 where

module A where
  postulate
    D    : Set
    _≡_  : D → D → Set
    a b  : D

  postulate p : a ≡ b

module B where
  open A
  {-# ATP axiom p #-}

open A

-- It doesn't works! The conjecture shouldn't be proved because the
-- ATP pragma isn't in scope.
postulate foo : a ≡ b
{-# ATP prove foo #-}
