------------------------------------------------------------------------------
-- The map-iterate property: A property using coinduction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property (Gibbons and Hutton 2005):
-- map f (iterate f x) = iterate f (f · x)

-- References:
--
-- • Eduardo Giménez and Pierre Castéran. A Tutorial on [Co-]Inductive
--   Types in Coq. May 1998 -- August 17, 2007.
--
-- • Jeremy Gibbons and Graham Hutton. Proof methods for corecursive
--   programs. Fundamenta Informaticae, XX:1–14, 2005.

module FOTC.Program.MapIterate.MapIterateATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- The map-iterate property.

≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind B prf₁ prf₂
  where
  -- Based on the relation used by (Giménez and Castéran, 2007).
  B : D → D → Set
  B xs ys = ∃[ y ] xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y)
  {-# ATP definition B #-}

  postulate
    prf₁ : ∀ {xs ys} → B xs ys →
           ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'
  {-# ATP prove prf₁ #-}

  postulate prf₂ : B (map f (iterate f x)) (iterate f (f · x))
  {-# ATP prove prf₂ #-}
