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
open import FOTC.Data.Stream
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
alter≈alter' = ≈-coind A h₁ h₂
  where
  -- TODO (25 November 2013): We are choosing a very trivial property,
  -- but it works!
  A : D → D → Set
  A xs ys = xs ≡ xs

  h₁ : A alter alter' → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
         alter ≡ x' ∷ xs' ∧ alter' ≡ x' ∷ ys' ∧ A xs' ys'
  h₁ Aaa' = true
            , false ∷ alter
            , map not₀ alter'
            , alter-eq
            , alter'-eq
            , refl

  h₂ : A alter alter'
  h₂ = refl
