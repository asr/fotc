------------------------------------------------------------------------------
-- Testing the erasing of proof terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module ProofTerm3 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

postulate foo : ∀ {m n} → (Nm : N m) → (Nn : N n) → ∀ {i} → N i → i ≡ i
{-# ATP prove foo #-}
