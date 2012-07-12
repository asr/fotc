------------------------------------------------------------------------------
-- Testing Agda internal terms: Lam
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The following conjecture uses the internal Agda term @Lam@.

module AgdaInternalTerms.LamTerm where

postulate
  D : Set
  ∃ : (D → Set) → Set  -- The existential quantifier type on D.
  A : D → Set

postulate ∃-intro : (t : D) → A t → ∃ A
{-# ATP prove ∃-intro #-}
