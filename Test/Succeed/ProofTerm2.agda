------------------------------------------------------------------------------
-- Testing the erasure of proof terms
------------------------------------------------------------------------------

module Test.Succeed.ProofTerm2 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

postulate foo : ∀ {m n} → (Nm : N m) → (Nn : N n) → m ≡ m
{-# ATP prove foo #-}
