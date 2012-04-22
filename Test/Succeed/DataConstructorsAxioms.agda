------------------------------------------------------------------------------
-- Testing the use of ATP axioms with data constructors
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.DataConstructorsAxioms where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN : N zero
  sN : ∀ {n} → N n → N (succ n)
{-# ATP axiom zN #-}
{-# ATP axiom sN #-}

postulate
  0-N : N zero
  1-N : N (succ zero)
{-# ATP prove 0-N #-}
{-# ATP prove 1-N #-}
