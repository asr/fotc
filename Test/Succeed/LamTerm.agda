------------------------------------------------------------------------------
-- Testing Agda internal terms: Lam
------------------------------------------------------------------------------

-- The following conjecture uses the internal Agda term Lam.

module Test.Succeed.LamTerm where

postulate
  D : Set
  ∃ : (D → Set) → Set  -- The existential quantifier type on D.
  A : D → Set

postulate ∃-intro : (t : D) → A t → ∃ A
{-# ATP prove ∃-intro #-}
