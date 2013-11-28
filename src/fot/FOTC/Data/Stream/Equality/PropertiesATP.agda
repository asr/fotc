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

≈→Stream₁ : ∀ {xs ys} → xs ≈ ys → Stream xs
≈→Stream₁ {xs} {ys} h = Stream-coind A h' refl
  where
  A : D → Set
  A ws = ws ≡ ws
  {-# ATP definition A #-}

  postulate h' : A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  {-# ATP prove h' #-}

≈→Stream₂ : ∀ {xs ys} → xs ≈ ys → Stream ys
≈→Stream₂ {xs} {ys} h = Stream-coind A h' refl
  where
  A : D → Set
  A ws = ws ≡ ws
  {-# ATP definition A #-}

  postulate h' : A ys → ∃[ x' ] ∃[ ys' ] ys ≡ x' ∷ ys' ∧ A ys'
  {-# ATP prove h' #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = ≈→Stream₁ h , ≈→Stream₂ h
