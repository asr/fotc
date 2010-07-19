------------------------------------------------------------------------------
-- Testing the use of general hints
------------------------------------------------------------------------------

module Test.Succeed.OnlyAxioms.GeneralHints where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN : N zero
  sN : (n : D) → N n → N (succ n)
-- The data constructors are general hints. They are translate as axioms.
{-# ATP hint zN #-}
{-# ATP hint sN #-}
