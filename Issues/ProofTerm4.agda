------------------------------------------------------------------------------
-- Testing the erasure of proof terms
------------------------------------------------------------------------------

module Issues.Tmp.ProofTerm4 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set
  _∷_ : D → D → D

data ListN : D → Set where
  consLN : ∀ {n ns} → N n → (LNns : ListN ns) → ListN (n ∷ ns)
{-# ATP axiom consLN #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
