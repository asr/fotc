------------------------------------------------------------------------------
-- The map-iterate property: A property using co-induction
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- The map-iterate property (Gibbons and Hutton, 2005):
-- map f (iterate f x) = iterate f (f · x)

module Combined.FOTC.Program.MapIterate.MapIterate where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.List
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type

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
-- Corecursive Programs. Fundamenta Informaticae XX, pp. 1–14.
