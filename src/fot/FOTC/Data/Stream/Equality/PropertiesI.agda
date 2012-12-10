------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity
open import FOTC.Relation.Binary.Bisimilarity.PropertiesI

------------------------------------------------------------------------------

stream-≡→≈ : ∀ {xs ys} → Stream xs → Stream ys → xs ≡ ys → xs ≈ ys
stream-≡→≈ Sxs _ refl = ≈-refl Sxs

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = Stream-coind A₁ h₁ (ys , h) , Stream-coind A₂ h₂ (xs , h)
  where
  A₁ : D → Set
  A₁ ws = ∃[ zs ] ws ≈ zs

  h₁ : ∀ {ws} → A₁ ws → ∃[ w' ] ∃[ ws' ] A₁ ws' ∧ ws ≡ w' ∷ ws'
  h₁ {ws} (zs , h₁) with ≈-unf h₁
  ... | w' , ws' , zs' , prf₁ , prf₂ , _ = w' , ws' , (zs' , prf₁) , prf₂

  A₂ : D → Set
  A₂ zs = ∃[ ws ] ws ≈ zs

  h₂ : ∀ {zs} → A₂ zs → ∃[ z' ] ∃[ zs' ] A₂ zs' ∧ zs ≡ z' ∷ zs'
  h₂  {zs} (ws , h₁) with ≈-unf h₁
  ... | w' , ws' , zs' , prf₁ , _ , prf₂ = w' , zs' , (ws' , prf₁) , prf₂
