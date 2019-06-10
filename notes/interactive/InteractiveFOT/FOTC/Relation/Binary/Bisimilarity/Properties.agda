------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Relation.Binary.Bisimilarity.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Base.List.Properties
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------

{-# TERMINATING #-}
≈→≡ : ∀ {xs ys} → xs ≈ ys → xs ≡ ys
≈→≡ {xs} {ys} h with ≈-out h
... | x' , xs' , ys' , prf₁ , prf₂ , prf₃ =
  xs       ≡⟨ prf₁ ⟩
  x' ∷ xs' ≡⟨ ∷-rightCong (≈→≡ prf₃) ⟩
  x' ∷ ys' ≡⟨ sym prf₂ ⟩
  ys       ∎
