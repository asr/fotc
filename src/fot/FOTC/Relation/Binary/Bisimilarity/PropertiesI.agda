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
≈-refl {xs} Sxs = ≈-coind B h refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs

  h : B xs xs →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ xs ≡ x' ∷ ys' ∧ B xs' ys'
  h _ with Stream-unf Sxs
  ... | x' , xs' , prf , _ = x' , xs' , xs' , prf , prf , refl

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind B h refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs

  h : B ys xs →
      ∃[ y' ] ∃[ ys' ] ∃[ xs' ] ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ B ys' xs'
  h _ with ≈-unf xs≈ys
  ... | x' , xs' , ys' , prf₁ , prf₂ , _ = x' , ys' , xs' , prf₂ , prf₁ , refl


≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind B h refl
  where
  B : D → D → Set
  B xs zs = xs ≡ xs

  h : B xs zs →
      ∃[ x' ] ∃[ xs' ] ∃[ zs' ] xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs' ∧ B xs' zs'
  h _ with ≈-unf xs≈ys
  ... | x' , xs' , ys' , prf₁ , prf₂ , _ with ≈-unf ys≈zs
  ... | y' , ys'' , zs' , prf₃ , prf₄ , _ =
    x'
    , xs'
    , zs'
    , prf₁
    , subst (λ t → zs ≡ t ∷ zs') y'≡x' prf₄
    , refl

    where
    y'≡x' : y' ≡ x'
    y'≡x' = ∧-proj₁ (∷-injective (trans (sym prf₃) prf₂))

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
                (subst (_≈_ xs') (sym ys≡ys') prf₃)

∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
∷-rightCong≈ {x} {xs} {ys} h = ≈-pre-fixed (x , xs , ys , refl , refl , h)
