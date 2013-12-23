{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Relation.Binary.Bisimilarity.TrivialBisimulation where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream.Type
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

h : ∀ {xs} → Stream xs → xs ≡ xs →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ xs ≡ x' ∷ ys' ∧ xs' ≡ xs'
h Sxs _ with Stream-unf Sxs
... | x' , xs' , xs≡x'∷xs' , _ = x' , xs' , xs' , xs≡x'∷xs' , xs≡x'∷xs' , refl

-- Andrés: Is λ ys _ → ys ≡ ys a bisimulation?
--
-- Peter: It is just a bisimulation on the subset Stream xs.
≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl Sxs = ≈-coind (λ ys _ → ys ≡ ys) (h Sxs) refl

------------------------------------------------------------------------------
-- Trivial binary relation, that is, R = D × D.
R : D → D → Set
R t _ = t ≡ t

-- ∀ s t. (s, t) ∈ R.
sRt : (s t : D) → R s t
sRt _ _ = refl
