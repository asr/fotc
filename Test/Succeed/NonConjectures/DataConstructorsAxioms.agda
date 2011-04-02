------------------------------------------------------------------------------
-- Testing the use of ATP <axioms> with data constructors
------------------------------------------------------------------------------

module Test.Succeed.NonConjectures.DataConstructorsAxioms where

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN : N zero
  sN : (n : D) → N n → N (succ n)
{-# ATP axiom zN #-}
{-# ATP axiom sN #-}

-- Testing a data constructor with holes.
data _×_ ( A B : Set) : Set where
  _,_ : A → B → A × B

data WithHoles : D × D → Set where
  withHoles : (x y : D) → WithHoles ( x , y )
{-# ATP axiom withHoles #-}
