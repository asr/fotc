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
x∷xs≈x∷ys→xs≈ys {x} {xs} {ys} x∷xs≈x∷ys with (≈-gfp₁ x∷xs≈x∷ys)
...| (x' , xs' , ys' , xs'≈ys' , x∷xs≡x'∷xs' , x∷ys≡x'∷ys') = xs≈ys
  where
  xs≡xs' : xs ≡ xs'
  xs≡xs' = ∧-proj₂ (∷-injective x∷xs≡x'∷xs')

  ys≡ys' : ys ≡ ys'
  ys≡ys' = ∧-proj₂ (∷-injective x∷ys≡x'∷ys')

  xs≈ys : xs ≈ ys
  xs≈ys = subst (λ t → t ≈ ys)
                (sym xs≡xs')
                (subst (λ t → xs' ≈ t) (sym ys≡ys') xs'≈ys')

xs≈ys→x∷xs≈x∷ys : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
xs≈ys→x∷xs≈x∷ys {x} {xs} {ys} xs≈ys =
  ≈-gfp₃ (x , xs , ys , xs≈ys , refl , refl)
