------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.Equality.PropertiesI where

open import Common.Function
open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

-- 2012-02-28. We required the existential witness on a pattern matching.
x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
x∷xs≈x∷ys→xs≈ys {x} {xs} {ys} h with (≈-gfp₁ h)
... | ∃-intro (∃-intro {xs'} (∃-intro {ys'} (prf₁ , prf₂ , prf₃))) = xs≈ys
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
xs≈ys→x∷xs≈x∷ys h = ≈-gfp₃ $ ∃-intro $ ∃-intro $ ∃-intro $ h , refl , refl
