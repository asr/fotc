------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

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
≈-in : ∀ {xs ys} →
       ∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
         (xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys') →
       xs ≈ ys
≈-in h = ≈-coind B h' h
  where
  B : D → D → Set
  B xs ys = ∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
              (xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys')

  h' : ∀ {xs} {ys} → B xs ys →
       ∃[ x' ] ∃[ xs' ] ∃[ ys' ] (xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys')
  h' (x' , xs' , ys' , prf₁ , prf₂ , xs'≈ys') =
    x' , xs' , ys' , prf₁ , prf₂ , ≈-out xs'≈ys'

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs ys = Stream xs ∧ xs ≡ ys

  h₁ : ∀ {xs ys} → B xs ys →
       ∃[ x' ] ∃[ xs' ] ∃[ ys' ] (xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys')
  h₁ (Sxs , refl) with Stream-out Sxs
  ... | x' , xs' , prf , Sxs' =
    x' , xs' , xs' , prf , prf , (Sxs' , refl)

  h₂ : B xs xs
  h₂ = Sxs , refl

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs ys = ys ≈ xs

  h₁ : ∀ {ys xs} → B ys xs →
       ∃[ y' ] ∃[ ys' ] ∃[ xs' ] (ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ B ys' xs')
  h₁ Bxsys with ≈-out Bxsys
  ... | y' , ys' , xs' , prf₁ , prf₂ , ys'≈xs' =
    y' , xs' , ys' , prf₂ , prf₁ , ys'≈xs'

  h₂ : B ys xs
  h₂ = xs≈ys

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs zs = ∃[ ys ] (xs ≈ ys ∧ ys ≈ zs)

  h₁ : ∀ {as} {cs} → B as cs →
       ∃[ a' ] ∃[ as' ] ∃[ cs' ] (as ≡ a' ∷ as' ∧ cs ≡ a' ∷ cs' ∧ B as' cs')
  h₁ {cs = cs} (bs , as≈bs , bs≈cs) with ≈-out as≈bs
  ... | a' , as' , bs' , prf₁ , prf₂ , as'≈bs' with ≈-out bs≈cs
  ... | b' , bs'' , cs' , prf₃ , prf₄ , bs''≈cs' =
    a'
    , as'
    , cs'
    , prf₁
    , subst (λ t → cs ≡ t ∷ cs') b'≡a' prf₄
    , (bs' , as'≈bs' , subst (λ t → t ≈ cs') bs''≡bs' bs''≈cs')
    where
    b'≡a' : b' ≡ a'
    b'≡a' = ∧-proj₁ (∷-injective (trans (sym prf₃) prf₂))

    bs''≡bs' : bs'' ≡ bs'
    bs''≡bs' = ∧-proj₂ (∷-injective (trans (sym prf₃) prf₂))

  h₂ : B xs zs
  h₂ = ys , (xs≈ys , ys≈zs)

∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
∷-injective≈ {x} {xs} {ys} h with ≈-out h
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
∷-rightCong≈ {x} {xs} {ys} h = ≈-in (x , xs , ys , refl , refl , h)
