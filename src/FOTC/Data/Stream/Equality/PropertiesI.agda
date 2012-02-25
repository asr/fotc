------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
x∷xs≈x∷ys→xs≈ys {x} {xs} {ys} h with (≈-gfp₁ h)
... | x' ,, xs' ,, ys' ,, prf₁ , prf₂ , prf₃ = xs≈ys
  where
  xs≡xs' : xs ≡ xs'
  xs≡xs' = ∧-proj₂ (∷-injective prf₂)

  ys≡ys' : ys ≡ ys'
  ys≡ys' = ∧-proj₂ (∷-injective prf₃)

  xs≈ys : xs ≈ ys
  xs≈ys = subst (λ t → t ≈ ys)
                (sym xs≡xs')
                (subst (λ t → xs' ≈ t) (sym ys≡ys') prf₁)

xs≈ys→x∷xs≈x∷ys : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
xs≈ys→x∷xs≈x∷ys {x} {xs} {ys} h = ≈-gfp₃ (x ,, xs ,, ys ,, h , refl , refl)
