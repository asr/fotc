------------------------------------------------------------------------------
-- Testing the erasing of proof terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module ProofTerm1 where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

postulate foo : ∀ {n} → (Nn : N n) → n ≡ n
{-# ATP prove foo #-}
