------------------------------------------------------------------------------
-- Testing the translation of data constructors
------------------------------------------------------------------------------

module Test.Succeed.NonConjectures.DataConstructors where

------------------------------------------------------------------------------

postulate
  D : Set

-- Testing a data constructor with holes.
data _×_ ( A B : Set) : Set where
  _,_ : A → B → A × B

data WithHoles : D × D → Set where
  withHoles : (x y : D) → WithHoles ( x , y )
{-# ATP hint withHoles #-}
