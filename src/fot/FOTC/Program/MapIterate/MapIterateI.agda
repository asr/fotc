------------------------------------------------------------------------------
-- The map-iterate property: A property using co-induction
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- The map-iterate property (Gibbons and Hutton, 2005):
-- map f (iterate f x) = iterate f (f · x)

module FOTC.Program.MapIterate.MapIterateI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream.Type
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------

unfoldMapIterate : ∀ f x →
                   map f (iterate f x) ≡ f · x ∷ map f (iterate f (f · x))
unfoldMapIterate f x =
  map f (iterate f x)               ≡⟨ mapCong₂ (iterate-eq f x) ⟩
  map f (x ∷ iterate f (f · x))     ≡⟨ map-∷ f x (iterate f (f · x)) ⟩
  f · x ∷ map f (iterate f (f · x)) ∎

map-iterate-Stream : ∀ f x → Stream (map f (iterate f x))
map-iterate-Stream f x = Stream-coind A h (x , refl)
  where
  A : D → Set
  A xs = ∃[ y ] (xs ≡ map f (iterate f y))

  h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] (xs ≡ x' ∷ xs' ∧ A xs')
  h (y , prf) = f · y
                , map f (iterate f (f · y))
                , trans prf (unfoldMapIterate f y)
                , f · y , refl

iterate-Stream : ∀ f x → Stream (iterate f (f · x))
iterate-Stream f x = Stream-coind A h (x , refl)
  where
  A : D → Set
  A xs = ∃[ y ] (xs ≡ iterate f (f · y))

  h : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] (xs ≡ x' ∷ xs' ∧ A xs')
  h (y , prf) = f · y
                , iterate f (f · (f · y))
                , trans prf (iterate-eq f (f · y))
                , f · y , refl

-- The map-iterate property.
≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind B h (x , refl , refl)
  where
  -- Based on the relation used by (Giménez and Castéran, 2007).
  B : D → D → Set
  B xs ys = ∃[ y ] (xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y))

  h : ∀ {xs} {ys} → B xs ys →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] (xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys')
  h (y , prf₁ , prf₂) =
      f · y
    , map f (iterate f (f · y))
    , iterate f (f · (f · y))
    , trans prf₁ (unfoldMapIterate f y)
    , trans prf₂ (iterate-eq f (f · y))
    , ((f · y) , refl , refl)

------------------------------------------------------------------------------
-- References
--
-- Giménez, Eduardo and Casterán, Pierre (2007). A Tutorial on
-- [Co-]Inductive Types in Coq.
--
-- Gibbons, Jeremy and Hutton, Graham (2005). Proof Methods for
-- Corecursive Programs. Fundamenta Informaticae XX, pp. 1–14.
