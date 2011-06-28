------------------------------------------------------------------------------
-- Bisimilarity properties
------------------------------------------------------------------------------

module Draft.FOTC.Data.Stream.Bisimilarity.PropertiesATP where

open import FOTC.Base

open import Draft.FOTC.Data.Stream.Bisimilarity using ( _≈_ )

------------------------------------------------------------------------------

postulate x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove x∷xs≈x∷ys→xs≈ys #-}
