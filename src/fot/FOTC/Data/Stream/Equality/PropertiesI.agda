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
≈→Stream {xs} {ys} h = Stream-coind A₁ prf₁ (ys , h)
                       , Stream-coind A₂ prf₂ (xs , h)
  where
  A₁ : D → Set
  A₁ ws = ∃[ zs ] ws ≈ zs

  prf₁ : A₁ xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A₁ xs'
  prf₁ (_ , h) with ≈-unf h
  ... | x' , xs' , zs' , h₁ , h₂ , h₃ = x' , xs' , h₁ , (zs' , h₃)

  A₂ : D → Set
  A₂ zs = ∃[ ws ] ws ≈ zs

  prf₂ : A₂ ys → ∃[ y' ] ∃[ ys' ] ys ≡ y' ∷ ys' ∧ A₂ ys'
  prf₂  (_ , h) with ≈-unf h
  ... | y' , ys' , zs' , h₁ , h₂ , h₃ = y' , zs' , h₂ , (ys' , h₃)
