------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

module FOTC.Data.Stream.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

postulate
  x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
{-# ATP prove x∷xs≈x∷ys→xs≈ys #-}

postulate
  xs≈ys→x∷xs≈x∷ys : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove xs≈ys→x∷xs≈x∷ys ≈-gfp₃ #-}
