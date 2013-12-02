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

≈→Stream₁ : ∀ {xs ys} → xs ≈ ys → Stream xs
≈→Stream₁ {xs} {ys} h = Stream-coind (λ zs → zs ≡ zs) h' refl
  where
  h' : xs ≡ xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ xs' ≡ xs'
  h' _ with ≈-unf h
  ... | x' , xs' , ys' , prf , _ = x' , xs' , prf , refl

≈→Stream₂ : ∀ {xs ys} → xs ≈ ys → Stream ys
≈→Stream₂ {xs} {ys} h = Stream-coind (λ zs → zs ≡ zs) h' refl
  where
  h' : ys ≡ ys → ∃[ x' ] ∃[ ys' ] ys ≡ x' ∷ ys' ∧ ys' ≡ ys'
  h' _ with ≈-unf h
  ... | x' , xs' , ys' , _ , prf , _ = x' , ys' , prf , refl

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = ≈→Stream₁ h , ≈→Stream₂ h
