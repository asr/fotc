------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind R prf₁ prf₂
  where
  R : D → D → Set
  R xs ys = Stream xs ∧ xs ≡ ys

  prf₁ : ∀ {xs ys} → R xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
         R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  prf₁ (Sxs , refl) with Stream-unf Sxs
  ... | x' , xs' , Sxs' , prf = x' , xs' , xs' , (Sxs' , refl) , prf , prf

  prf₂ : R xs xs
  prf₂ = Sxs , refl


≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind R prf₁ prf₂
  where
  R : D → D → Set
  R xs ys = ys ≈ xs

  prf₁ : R ys xs →
         ∃[ y' ] ∃[ ys' ] ∃[ xs' ]
         R ys' xs' ∧ ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs'
  prf₁ Rxsys with ≈-unf Rxsys
  ... | y' , ys' , xs' , ys'≈xs' , h₁ , h₂ =
    y' , xs' , ys' , ys'≈xs' , h₂ , h₁

  prf₂ : R ys xs
  prf₂ = xs≈ys

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind R prf₁ prf₂
  where
  R : D → D → Set
  R xs zs = ∃[ ys ] xs ≈ ys ∧ ys ≈ zs

  prf₁ : R xs zs →
         ∃[ x' ] ∃[ xs' ] ∃[ zs' ]
         R xs' zs' ∧ xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs'
  prf₁ (ys , xs≈ys , ys≈zs) with ≈-unf xs≈ys
  ... | x' , xs' , ys' , xs'≈ys' , prf₁ , prf₂ with ≈-unf ys≈zs
  ... | y' , ys'' , zs' , ys''≈zs' , prf₃ , prf₄ =
    x'
    , xs'
    , zs'
    , (ys' , (xs'≈ys' , (subst (λ t → t ≈ zs') ys''≡ys' ys''≈zs')))
    , prf₁
    , subst (λ t → zs ≡ t ∷ zs') y'≡x' prf₄

    where
    y'≡x' : y' ≡ x'
    y'≡x' = ∧-proj₁ (∷-injective (trans (sym prf₃) prf₂))

    ys''≡ys' : ys'' ≡ ys'
    ys''≡ys' = ∧-proj₂ (∷-injective (trans (sym prf₃) prf₂))

  prf₂ : R xs zs
  prf₂ = ys , (xs≈ys , ys≈zs)

∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
∷-injective≈ {x} {xs} {ys} h with ≈-unf h
... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ = xs≈ys
  where
  xs≡xs' : xs ≡ xs'
  xs≡xs' = ∧-proj₂ (∷-injective prf₂)

  ys≡ys' : ys ≡ ys'
  ys≡ys' = ∧-proj₂ (∷-injective prf₃)

  xs≈ys : xs ≈ ys
  xs≈ys = subst (λ t → t ≈ ys)
                (sym xs≡xs')
                (subst (λ t → xs' ≈ t) (sym ys≡ys') prf₁)

∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
∷-rightCong≈ {x} {xs} {ys} h = ≈-pre-fixed (x , xs , ys , h , refl , refl)
