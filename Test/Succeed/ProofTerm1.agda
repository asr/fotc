------------------------------------------------------------------------------
-- Testing the erasure of proof terms
------------------------------------------------------------------------------

module Issues.Tmp.ProofTerm1 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

postulate
  foo : ∀ {n} → (Nn : N n) → n ≡ n
{-# ATP prove foo #-}
