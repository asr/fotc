------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity
open import FOTC.Relation.Binary.Bisimilarity.PropertiesATP

------------------------------------------------------------------------------

postulate stream-≡→≈ : ∀ {xs ys} → Stream xs → Stream ys → xs ≡ ys → xs ≈ ys
{-# ATP prove stream-≡→≈ ≈-refl #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = Stream-coind A₁ h₁ (ys , h)
                       , Stream-coind A₂ h₂ (xs , h)
  where
  A₁ : D → Set
  A₁ ws = ∃[ zs ] ws ≈ zs
  {-# ATP definition A₁ #-}

  postulate h₁ : A₁ xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A₁ xs'
  {-# ATP prove h₁ #-}

  A₂ : D → Set
  A₂ zs = ∃[ ws ] ws ≈ zs
  {-# ATP definition A₂ #-}

  postulate h₂ : A₂ ys → ∃[ y' ] ∃[ ys' ] ys ≡ y' ∷ ys' ∧ A₂ ys'
  {-# ATP prove h₂ #-}
