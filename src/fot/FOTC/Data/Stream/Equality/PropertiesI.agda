------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Stream.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream.Type
open import FOTC.Relation.Binary.Bisimilarity.PropertiesI
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------

stream-≡→≈ : ∀ {xs ys} → Stream xs → Stream ys → xs ≡ ys → xs ≈ ys
stream-≡→≈ Sxs _ refl = ≈-refl Sxs

≈→Stream₁ : ∀ {xs ys} → xs ≈ ys → Stream xs
≈→Stream₁ {xs} {ys} h = Stream-coind A h' (ys , h)
   where
   A : D → Set
   A ws = ∃[ zs ] ws ≈ zs

   h' : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
   h' (_ , Axs) with ≈-out Axs
   ... | x' , xs' , zs' , prf₁ , prf₂ , prf₃ = x' , xs' , prf₁ , (zs' , prf₃)

≈→Stream₂ : ∀ {xs ys} → xs ≈ ys → Stream ys
≈→Stream₂ {xs} {ys} h = Stream-coind A h' (xs , h)
   where
   A : D → Set
   A zs = ∃[ ws ] ws ≈ zs

   h' : ∀ {ys} → A ys → ∃[ y' ] ∃[ ys' ] ys ≡ y' ∷ ys' ∧ A ys'
   h'  (_ , Ays) with ≈-out Ays
   ... | y' , ys' , zs' , prf₁ , prf₂ , prf₃ = y' , zs' , prf₂ , (ys' , prf₃)

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = ≈→Stream₁ h , ≈→Stream₂ h
