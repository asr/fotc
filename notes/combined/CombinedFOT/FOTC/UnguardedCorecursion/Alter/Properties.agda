------------------------------------------------------------------------------
-- Properties of the alter list
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombinedFOT.FOTC.UnguardedCorecursion.Alter.Properties where

open import CombinedFOT.FOTC.UnguardedCorecursion.Alter.Alter

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Stream.Type
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- TODO (23 December 2013).
-- alter-Stream : Stream alter
-- alter-Stream = Stream-coind A h refl
--   where
--   A : D → Set
--   A xs = xs ≡ xs
--   {-# ATP definition A #-}

--   postulate h : A alter → ∃[ x' ] ∃[ xs' ] alter ≡ x' ∷ xs' ∧ A xs'
--   {-# ATP prove h #-}

-- TODO (23 December 2013).
-- alter'-Stream : Stream alter'
-- alter'-Stream = Stream-coind A h refl
--   where
--   A : D → Set
--   A xs = xs ≡ xs
--   {-# ATP definition A #-}

--   postulate h : A alter' → ∃[ x' ] ∃[ xs' ] alter' ≡ x' ∷ xs' ∧ A xs'
--   {-# ATP prove h #-}

-- TODO (23 December 2013).
-- alter≈alter' : alter ≈ alter'
-- alter≈alter' = ≈-coind B h₁ h₂
--   where
--   B : D → D → Set
--   B xs ys = xs ≡ xs
--   {-# ATP definition B #-}

--   postulate h₁ : B alter alter' → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
--                    alter ≡ x' ∷ xs' ∧ alter' ≡ x' ∷ ys' ∧ B xs' ys'
--   {-# ATP prove h₁ #-}

--   postulate h₂ : B alter alter'
--   {-# ATP prove h₂ #-}
