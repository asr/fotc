------------------------------------------------------------------------------
-- Bisimilarity properties
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimilarity.PropertiesATP where

open import LTC.Base

open import LTC.Data.Stream.Bisimilarity using ( _≈_ )

------------------------------------------------------------------------------

postulate
  x∷xs≈x∷ys→xs≈ys : {x xs ys : D} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove x∷xs≈x∷ys→xs≈ys #-}
