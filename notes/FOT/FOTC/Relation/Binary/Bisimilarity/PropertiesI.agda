------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Relation.Binary.Bisimilarity.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
≈→≡ : ∀ {xs ys} → xs ≈ ys → xs ≡ ys
≈→≡ {xs} {ys} h with ≈-unf h
... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ =
  xs       ≡⟨ prf₁ ⟩
  x' ∷ xs' ≡⟨ ∷-rightCong (≈→≡ prf₃) ⟩
  x' ∷ ys' ≡⟨ sym prf₂ ⟩
  ys       ∎
