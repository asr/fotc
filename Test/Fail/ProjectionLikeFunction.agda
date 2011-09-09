------------------------------------------------------------------------------
-- The translation of projection-like functions is not implemented
------------------------------------------------------------------------------

module Test.Fail.ProjectionLikeFunction where

-- Error: The translation of projection-like functions Test.Fail.ProjectionLikeFunction._.P is not implemented.

postulate
  D    : Set
  _≡_  : D → D → Set
  N    : D → Set

foo : ∀ {n} → N n → D
foo {n} Nn = n
  where
  P : D → Set
  P i = i ≡ i
  {-# ATP definition P #-}

  postulate bar : P n
  {-# ATP prove bar #-}