------------------------------------------------------------------------------
-- Trivial theorem used by the shelltestrunner test
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module TrivialTheorem where

postulate
  D   : Set
  _≡_ : D → D → Set
  a b : D

postulate p : a ≡ b
{-# ATP axiom p #-}

postulate foo : a ≡ b
{-# ATP prove foo #-}
