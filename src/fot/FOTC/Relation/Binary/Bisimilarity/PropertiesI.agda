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
open import FOTC.Data.Stream.Type
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
-- point of the bisimulation functional (see
-- FOTC.Relation.Binary.Bisimulation).
≈-pre-fixed : ∀ {xs ys} →
              (∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
                xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys') →
              xs ≈ ys
≈-pre-fixed {xs} {ys} h = ≈-coind (λ zs _ → zs ≡ zs) h' refl
  where
  h' : xs ≡ xs →
       ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≡ xs'
  h' _ with h
  ... | x' , xs' , ys' , prf₁ , prf₂ , _ = x' , xs' , ys' , prf₁ , prf₂ , refl

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind (λ ys _ → ys ≡ ys) h refl
  where
  h : xs ≡ xs →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ xs ≡ x' ∷ ys' ∧ xs' ≡ xs'
  h _ with Stream-unf Sxs
  ... | x' , xs' , prf , _ = x' , xs' , xs' , prf , prf , refl

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind (λ zs _ → zs ≡ zs) h refl
  where
  h : ys ≡ ys →
      ∃[ y' ] ∃[ ys' ] ∃[ xs' ] ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ ys' ≡ ys'
  h _ with ≈-unf xs≈ys
  ... | x' , xs' , ys' , prf₁ , prf₂ , _ = x' , ys' , xs' , prf₂ , prf₁ , refl


≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind (λ ws _ → ws ≡ ws) h refl
  where
  h : xs ≡ xs →
      ∃[ x' ] ∃[ xs' ] ∃[ zs' ] xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs' ∧ xs' ≡ xs'
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
