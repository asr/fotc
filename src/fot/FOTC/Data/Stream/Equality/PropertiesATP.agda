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

------------------------------------------------------------------------------

stream-≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
stream-≈-refl {xs} Sxs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs ys = Stream xs ∧ xs ≡ ys
  {-# ATP definition R #-}

  postulate h₁ : ∀ {xs ys} → R xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
                 R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  {-# ATP prove h₁ #-}

  postulate h₂ : R xs xs
  {-# ATP prove h₂ #-}

postulate stream-≡→≈ : ∀ {xs ys} → Stream xs → Stream ys → xs ≡ ys → xs ≈ ys
{-# ATP prove stream-≡→≈ stream-≈-refl #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = Stream-coind A₁ h₁ (ys , h) , Stream-coind A₂ h₂ (xs , h)
  where
  A₁ : D → Set
  A₁ ws = ∃[ zs ] ws ≈ zs
  {-# ATP definition A₁ #-}

  postulate h₁ : ∀ {ws} → A₁ ws → ∃[ w' ] ∃[ ws' ] A₁ ws' ∧ ws ≡ w' ∷ ws'
  {-# ATP prove h₁ #-}

  A₂ : D → Set
  A₂ zs = ∃[ ws ] ws ≈ zs
  {-# ATP definition A₂ #-}

  postulate h₂ : ∀ {zs} → A₂ zs → ∃[ z' ] ∃[ zs' ] A₂ zs' ∧ zs ≡ z' ∷ zs'
  {-# ATP prove h₂ #-}
