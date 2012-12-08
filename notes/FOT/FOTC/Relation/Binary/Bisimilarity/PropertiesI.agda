------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}

module FOT.FOTC.Relation.Binary.Bisimilarity.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.PropertiesI
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
≈→≡₁ : ∀ {xs ys} → xs ≈ ys → xs ≡ ys
≈→≡₁ {xs} {ys} xs≈ys with (≈-unf xs≈ys)
... | x' , xs' , ys' , h₁ , h₂ , h₃ =
  xs       ≡⟨ h₂ ⟩
  x' ∷ xs' ≡⟨ ∷-rightCong (≈→≡₁ h₁) ⟩
  x' ∷ ys' ≡⟨ sym h₃ ⟩
  ys       ∎

-- Requires K.
{-# NO_TERMINATION_CHECK #-}
≈→≡₂ : ∀ {xs ys} → xs ≈ ys → xs ≡ ys
≈→≡₂ xs≈ys with (≈-unf xs≈ys)
... | x' , xs' , ys' , h , refl , refl = ∷-rightCong (≈→≡₂ h)
