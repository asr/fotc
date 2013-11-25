------------------------------------------------------------------------------
-- The map-iterate property: Testing a trivial relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property (Gibbons and Hutton, 2005):
-- map f (iterate f x) = iterate f (f · x)

-- References:
--
-- • Giménez, Eduardo and Casterán, Pierre (2007). A Tutorial on
--   [Co-]Inductive Types in Coq.
--
-- • Gibbons, Jeremy and Hutton, Graham (2005). Proof Methods for
--   Corecursive Programs. In: Fundamenta Informaticae XX, pp. 1–14.

module FOT.FOTC.Program.MapIterate.MapIterateTrivialRelation where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

unfoldMapIterate : ∀ f x →
                   map f (iterate f x) ≡ f · x ∷ map f (iterate f (f · x))
unfoldMapIterate f x =
  map f (iterate f x)               ≡⟨ mapCong₂ (iterate-eq f x) ⟩
  map f (x ∷ iterate f (f · x))     ≡⟨ map-∷ f x (iterate f (f · x)) ⟩
  f · x ∷ map f (iterate f (f · x)) ∎

-- The map-iterate property.
≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind B h refl
  where
  -- Trivial relation
  B : D → D → Set
  B xs ys = xs ≡ xs

  h : B (map f (iterate f x)) (iterate f (f · x)) → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
        map f (iterate f x) ≡ x' ∷ xs'
        ∧ iterate f (f · x) ≡ x' ∷ ys'
        ∧ B xs' ys'
  h _ = f · x
        , map f (iterate f (f · x))
        , iterate f (f · (f · x))
        , unfoldMapIterate f x
        , iterate-eq f (f · x)
        , refl
