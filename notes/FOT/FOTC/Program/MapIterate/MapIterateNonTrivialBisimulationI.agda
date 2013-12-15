------------------------------------------------------------------------------
-- The map-iterate property using a non-trivial bisimulation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property (Gibbons and Hutton, 2005):
-- map f (iterate f x) = iterate f (f · x)

module FOT.FOTC.Program.MapIterate.MapIterateNonTrivialBisimulationI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Relation.Binary.Bisimilarity
open import FOTC.Program.MapIterate.MapIterateI

------------------------------------------------------------------------------
-- The map-iterate property.
≈-map-iterate' : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate' f x = ≈-coind B h (x , refl , refl)
  where
  -- Based on the relation used by (Giménez and Castéran, 2007).
  B : D → D → Set
  B xs ys = ∃[ y ] xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y)

  h : B (map f (iterate f x)) (iterate f (f · x)) → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
        map f (iterate f x) ≡ x' ∷ xs'
        ∧ iterate f (f · x) ≡ x' ∷ ys'
        ∧ B xs' ys'
  h (y , prf) =
    f · y
    , map f (iterate f (f · y))
    , iterate f (f · (f · y))
    , trans (∧-proj₁ prf) (unfoldMapIterate f y)
    , trans (∧-proj₂ prf) (iterate-eq f (f · y))
    , ((f · y) , refl , refl)

------------------------------------------------------------------------------
-- References:
--
-- • Giménez, Eduardo and Casterán, Pierre (2007). A Tutorial on
--   [Co-]Inductive Types in Coq.
--
-- • Gibbons, Jeremy and Hutton, Graham (2005). Proof Methods for
--   Corecursive Programs. In: Fundamenta Informaticae XX, pp. 1–14.
