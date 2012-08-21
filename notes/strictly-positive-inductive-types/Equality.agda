module Equality where

-- Nils (Agda mailing list): According to Voevodsky this type is
-- incompatible with his univalent model.
data _≡_ (A : Set) : Set → Set where
  refl : A ≡ A
