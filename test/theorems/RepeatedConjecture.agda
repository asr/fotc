-- TODO: To add check for it to Agda.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module RepeatedConjecture where

postulate
  D    : Set
  _≡_  : D → D → Set
  refl : ∀ d → d ≡ d

-- The ATPs only try to prove the last ATP pragma.
postulate sym : ∀ d e → d ≡ e → e ≡ d
{-# ATP prove sym #-}
{-# ATP prove sym refl #-}
