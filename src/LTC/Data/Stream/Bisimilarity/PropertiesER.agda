------------------------------------------------------------------------------
-- Bisimilarity properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimilarity.PropertiesER where

open import LTC.Minimal
open import LTC.Minimal.Properties using (∷-injective)
open import LTC.MinimalER using ( subst )

open import LTC.Data.Stream.Bisimilarity using ( _≈_ ; -≈-gfp₁ )

------------------------------------------------------------------------------

x∷xs≈x∷ys→xs≈ys : {x xs ys : D} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
x∷xs≈x∷ys→xs≈ys {x} {xs} {ys} x∷xs≈x∷ys = xs≈ys
  where
    x' : D
    x' = ∃D-proj₁ (-≈-gfp₁ x∷xs≈x∷ys)

    xs' : D
    xs' = ∃D-proj₁ (∃D-proj₂ (-≈-gfp₁ x∷xs≈x∷ys))

    ys' : D
    ys' = ∃D-proj₁ (∃D-proj₂ (∃D-proj₂ (-≈-gfp₁ x∷xs≈x∷ys)))

    aux : xs' ≈ ys' ∧ x ∷ xs ≡ x' ∷ xs' ∧ x ∷ ys ≡ x' ∷ ys'
    aux = ∃D-proj₂ (∃D-proj₂ (∃D-proj₂ (-≈-gfp₁ x∷xs≈x∷ys)))

    xs'≈ys' : xs' ≈ ys'
    xs'≈ys' = ∧-proj₁ aux

    x∷xs≡x'∷xs' : x ∷ xs ≡ x' ∷ xs'
    x∷xs≡x'∷xs' = ∧-proj₁ (∧-proj₂ aux)

    x∷ys≡x'∷ys' : x ∷ ys ≡ x' ∷ ys'
    x∷ys≡x'∷ys' = ∧-proj₂ (∧-proj₂ aux)

    xs≡xs' : xs ≡ xs'
    xs≡xs' = ∧-proj₂ (∷-injective x∷xs≡x'∷xs')

    ys≡ys' : ys ≡ ys'
    ys≡ys' = ∧-proj₂ (∷-injective x∷ys≡x'∷ys')

    xs≈ys : xs ≈ ys
    xs≈ys = subst (λ t → t ≈ ys)
                  (sym xs≡xs')
                  (subst (λ t → xs' ≈ t) (sym ys≡ys') xs'≈ys')
