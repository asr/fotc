{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Relation.Binary.Bisimilarity.NonBisimulation where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

h : ∀ {xs} → Stream xs → xs ≡ xs →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ xs ≡ x' ∷ ys' ∧ xs' ≡ xs'
h Sxs _ with Stream-unf Sxs
... | x' , xs' , xs≡x'∷xs' , _ = x' , xs' , xs' , xs≡x'∷xs' , xs≡x'∷xs' , refl

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind (λ ys _ → ys ≡ ys) (h Sxs) refl
