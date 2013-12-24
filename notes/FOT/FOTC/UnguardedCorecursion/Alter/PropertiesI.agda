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
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- TODO (23 December 2013).
-- alter-Stream : Stream alter
-- alter-Stream = Stream-coind A h refl
--   where
--   A : D → Set
--   A xs = xs ≡ alter

--   h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
--   h Ax = true , (false ∷ alter) , trans Ax alter-eq , {!!}

-- TODO (23 December 2013).
-- alter≈alter' : alter ≈ alter'
-- alter≈alter' = ≈-coind B h₁ h₂
--   where
--   B : D → D → Set
--   B xs ys = xs ≡ xs

--   h₁ : B alter alter' → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
--          alter ≡ x' ∷ xs' ∧ alter' ≡ x' ∷ ys' ∧ B xs' ys'
--   h₁ _ = true
--          , false ∷ alter
--          , map not₀ alter'
--          , alter-eq
--          , alter'-eq
--          , refl

--   h₂ : B alter alter'
--   h₂ = refl
