------------------------------------------------------------------------------
-- Testing the erasure of proof terms
------------------------------------------------------------------------------

module Test.Succeed.ProofTerm5 where

postulate
  D          : Set
  _≡_        : D → D → Set
  Bool       : D → Set
  not        : D → D

-- In this case the proof term Bb is referenced in the types of the
-- definitions of as and bs via the where clause. Therefore in the
-- translation of as and bs, we need to erase this proof term.
foo : (a : D) → ∀ {b} → Bool b → D
foo  a Bb = a
  where
  c : D
  c = a
  {-# ATP definition c #-}

  d : D
  d = not c
  {-# ATP definition d #-}

  postulate bar : d ≡ not a
  {-# ATP prove bar #-}
