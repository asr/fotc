------------------------------------------------------------------------------
-- Properties of the alter list
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.UnguardedCorecursion.Alter.PropertiesI where

open import FOT.FOTC.UnguardedCorecursion.Alter.Alter

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Stream.Type
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

alter-Stream : Stream alter
alter-Stream = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs

  h : A alter → ∃[ x' ] ∃[ xs' ] alter ≡ x' ∷ xs' ∧ A xs'
  h _ = true , (false ∷ alter) , alter-eq , refl

alter≈alter' : alter ≈ alter'
alter≈alter' = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs ys = xs ≡ xs

  h₁ : B alter alter' → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
         alter ≡ x' ∷ xs' ∧ alter' ≡ x' ∷ ys' ∧ B xs' ys'
  h₁ _ = true
         , false ∷ alter
         , map not₀ alter'
         , alter-eq
         , alter'-eq
         , refl

  h₂ : B alter alter'
  h₂ = refl
