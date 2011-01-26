------------------------------------------------------------------------------
-- Bisimilarity properties
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimilarity.PropertiesATP where

open import LTC.Base

open import LTC.Data.Stream.Bisimilarity using ( _≈_ )

------------------------------------------------------------------------------

postulate
  x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove x∷xs≈x∷ys→xs≈ys #-}
