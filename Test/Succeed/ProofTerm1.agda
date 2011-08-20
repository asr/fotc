------------------------------------------------------------------------------
-- Testing the erasure of proof terms
------------------------------------------------------------------------------

module Test.Succeed.ProofTerm1 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

postulate foo : ∀ {n} → (Nn : N n) → n ≡ n
{-# ATP prove foo #-}
