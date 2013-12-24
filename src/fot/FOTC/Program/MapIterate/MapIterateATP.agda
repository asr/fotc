------------------------------------------------------------------------------
-- The map-iterate property: A property using co-induction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property (Gibbons and Hutton, 2005):
-- map f (iterate f x) = iterate f (f · x)

module FOTC.Program.MapIterate.MapIterateATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- The map-iterate property.
≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind B h₁ h₂
  where
  -- Based on the relation used by (Giménez and Castéran, 2007).
  B : D → D → Set
  B xs ys = ∃[ y ] xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y)
  {-# ATP definition B #-}

  postulate
    h₁ : ∀ {xs} {ys} → B xs ys →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'
  {-# ATP prove h₁ #-}

  postulate h₂ : B (map f (iterate f x)) (iterate f (f · x))
  {-# ATP prove h₂ #-}

------------------------------------------------------------------------------
-- References
--
-- Giménez, Eduardo and Casterán, Pierre (2007). A Tutorial on
-- [Co-]Inductive Types in Coq.
--
-- Gibbons, Jeremy and Hutton, Graham (2005). Proof Methods for
-- Corecursive Programs. In: Fundamenta Informaticae XX, pp. 1–14.
