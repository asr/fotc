------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Stream.Equality.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Stream.Type
open import Combined.FOTC.Relation.Binary.Bisimilarity.Properties
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type

  ------------------------------------------------------------------------------

postulate stream-≡→≈ : ∀ {xs ys} → Stream xs → Stream ys → xs ≡ ys → xs ≈ ys
{-# ATP prove stream-≡→≈ ≈-refl #-}

-- See Issue https://github.com/asr/apia/issues/81 .
≈→Stream₁A : D → Set
≈→Stream₁A ws = ∃[ zs ] ws ≈ zs
{-# ATP definition ≈→Stream₁A #-}

≈→Stream₁ : ∀ {xs ys} → xs ≈ ys → Stream xs
≈→Stream₁ {xs} {ys} h = Stream-coind ≈→Stream₁A h' (ys , h)
  where
  postulate h' : ∀ {xs} → ≈→Stream₁A xs →
                 ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ ≈→Stream₁A xs'
  {-# ATP prove h' #-}

-- See Issue https://github.com/asr/apia/issues/81 .
≈→Stream₂A : D → Set
≈→Stream₂A zs = ∃[ ws ] ws ≈ zs
{-# ATP definition ≈→Stream₂A #-}

≈→Stream₂ : ∀ {xs ys} → xs ≈ ys → Stream ys
≈→Stream₂ {xs} {ys} h = Stream-coind ≈→Stream₂A h' (xs , h)
  where
  postulate h' : ∀ {ys} → ≈→Stream₂A ys →
                 ∃[ y' ] ∃[ ys' ] ys ≡ y' ∷ ys' ∧ ≈→Stream₂A ys'
  {-# ATP prove h' #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = ≈→Stream₁ h , ≈→Stream₂ h
