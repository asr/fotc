------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity.PropertiesATP where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

postulate
  x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove x∷xs≈x∷ys→xs≈ys #-}

postulate
  xs≈ys→x∷xs≈x∷ys : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove xs≈ys→x∷xs≈x∷ys ≈-gfp₃ #-}
