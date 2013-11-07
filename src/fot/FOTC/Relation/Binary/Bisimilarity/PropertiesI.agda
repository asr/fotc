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
≈-refl {xs} Sxs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs ys = Stream xs ∧ xs ≡ ys

  h₁ : ∀ {xs ys} → R xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
         xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ R xs' ys'
  h₁ (Sxs , refl) with Stream-unf Sxs
  ... | x' , xs' , prf , Sxs' =
    x' , xs' , xs' , prf , prf , (Sxs' , refl)

  h₂ : R xs xs
  h₂ = Sxs , refl


≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs ys = ys ≈ xs

  h₁ : R ys xs →
       ∃[ y' ] ∃[ ys' ] ∃[ xs' ]
         ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ R ys' xs'
  h₁ Rxsys with ≈-unf Rxsys
  ... | y' , ys' , xs' , prf₁ , prf₂ , ys'≈xs' =
    y' , xs' , ys' , prf₂ , prf₁ , ys'≈xs'

  h₂ : R ys xs
  h₂ = xs≈ys

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs zs = ∃[ ys ] xs ≈ ys ∧ ys ≈ zs

  h₁ : R xs zs →
       ∃[ x' ] ∃[ xs' ] ∃[ zs' ]
         xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs' ∧ R xs' zs'
  h₁ (ys , xs≈ys , ys≈zs) with ≈-unf xs≈ys
  ... | x' , xs' , ys' , prf₁ , prf₂ , xs'≈ys' with ≈-unf ys≈zs
  ... | y' , ys'' , zs' , prf₃ , prf₄ , ys''≈zs' =
    x'
    , xs'
    , zs'
    , prf₁
    , subst (λ t → zs ≡ t ∷ zs') y'≡x' prf₄
    , (ys' , (xs'≈ys' , (subst (λ t → t ≈ zs') ys''≡ys' ys''≈zs')))

    where
    y'≡x' : y' ≡ x'
    y'≡x' = ∧-proj₁ (∷-injective (trans (sym prf₃) prf₂))

    ys''≡ys' : ys'' ≡ ys'
    ys''≡ys' = ∧-proj₂ (∷-injective (trans (sym prf₃) prf₂))

  h₂ : R xs zs
  h₂ = ys , (xs≈ys , ys≈zs)

∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
∷-injective≈ {x} {xs} {ys} h with ≈-unf h
... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ = xs≈ys
  where
  xs≡xs' : xs ≡ xs'
  xs≡xs' = ∧-proj₂ (∷-injective prf₁)

  ys≡ys' : ys ≡ ys'
  ys≡ys' = ∧-proj₂ (∷-injective prf₂)

  xs≈ys : xs ≈ ys
  xs≈ys = subst (λ t → t ≈ ys)
                (sym xs≡xs')
                (subst (λ t → xs' ≈ t) (sym ys≡ys') prf₃)

∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
∷-rightCong≈ {x} {xs} {ys} h = ≈-pre-fixed (x , xs , ys , refl , refl , h)
