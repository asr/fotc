------------------------------------------------------------------------------
-- Properties for the equality on streams
------------------------------------------------------------------------------

module FOTC.Data.Stream.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI using ( ∷-injective )

open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

x∷xs≈x∷ys→xs≈ys : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
x∷xs≈x∷ys→xs≈ys {x} {xs} {ys} x∷xs≈x∷ys = xs≈ys
  where
  x' : D
  x' = ∃-proj₁ (≈-gfp₁ x∷xs≈x∷ys)

  xs' : D
  xs' = ∃-proj₁ (∃-proj₂ (≈-gfp₁ x∷xs≈x∷ys))

  ys' : D
  ys' = ∃-proj₁ (∃-proj₂ (∃-proj₂ (≈-gfp₁ x∷xs≈x∷ys)))

  helper : xs' ≈ ys' ∧ x ∷ xs ≡ x' ∷ xs' ∧ x ∷ ys ≡ x' ∷ ys'
  helper = ∃-proj₂ (∃-proj₂ (∃-proj₂ (≈-gfp₁ x∷xs≈x∷ys)))

  xs'≈ys' : xs' ≈ ys'
  xs'≈ys' = ∧-proj₁ helper

  x∷xs≡x'∷xs' : x ∷ xs ≡ x' ∷ xs'
  x∷xs≡x'∷xs' = ∧-proj₁ (∧-proj₂ helper)

  x∷ys≡x'∷ys' : x ∷ ys ≡ x' ∷ ys'
  x∷ys≡x'∷ys' = ∧-proj₂ (∧-proj₂ helper)

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
