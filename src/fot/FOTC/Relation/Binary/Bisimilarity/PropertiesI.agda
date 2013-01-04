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
       R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  h₁ (Sxs , refl) with Stream-unf Sxs
  ... | x' , xs' , Sxs' , prf = x' , xs' , xs' , (Sxs' , refl) , prf , prf

  h₂ : R xs xs
  h₂ = Sxs , refl


≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs ys = ys ≈ xs

  h₁ : ∀ {xs ys} → R xs ys →
       ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
       R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  h₁ Rxsys with ≈-unf Rxsys
  ... | y' , ys' , xs' , ys'≈xs' , prf₁ , prf₂ =
    y' , xs' , ys' , ys'≈xs' , prf₂ , prf₁

  h₂ : R ys xs
  h₂ = xs≈ys

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs zs = ∃[ ys ] xs ≈ ys ∧ ys ≈ zs

  h₁ : ∀ {xs zs} → R xs zs →
       ∃[ x' ] ∃[ xs' ] ∃[ zs' ]
       R xs' zs' ∧ xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs'
  h₁ {zs = zs} (ys , xs≈ys , ys≈zs) with ≈-unf xs≈ys
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

  h₂ : R xs zs
  h₂ = ys , (xs≈ys , ys≈zs)

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
∷-rightCong≈ {x} {xs} {ys} h = ≈-gfp₃ (x , xs , ys , h , refl , refl)
