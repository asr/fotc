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

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = Stream-coind P₁ h₁ (ys , h) , Stream-coind P₂ h₂ (xs , h)
  where
  P₁ : D → Set
  P₁ ws = ∃[ zs ] ws ≈ zs
  {-# ATP definition P₁ #-}

  postulate h₁ : ∀ {ws} → P₁ ws → ∃[ w' ] ∃[ ws' ] P₁ ws' ∧ ws ≡ w' ∷ ws'
  {-# ATP prove h₁ #-}

  P₂ : D → Set
  P₂ zs = ∃[ ws ] ws ≈ zs
  {-# ATP definition P₂ #-}

  postulate h₂ : ∀ {zs} → P₂ zs → ∃[ z' ] ∃[ zs' ] P₂ zs' ∧ zs ≡ z' ∷ zs'
  {-# ATP prove h₂ #-}
