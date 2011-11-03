------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

module Test.Succeed.Definition09 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

data ∃ (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃ P

-- The predicate is not inside the where clause because the
-- translation of projection-like functions is not implemented.
P : D → Set
P d = ∃ λ e → e ≡ d
{-# ATP definition P #-}

-- We test the translation of a definition which Agda eta-reduces.
foo : ∀ {n} → N n → D
foo {n} Nn = n
  where
  postulate bar : ∀ {d} → P d → P d
  {-# ATP prove bar #-}
