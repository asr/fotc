------------------------------------------------------------------------------
-- The map-iterate property: A property using coinduction
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

module FOTC.Program.MapIterate.MapIterateI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

unfoldMap : ∀ f x → map f (iterate f x) ≡ f · x ∷ map f (iterate f (f · x))
unfoldMap f x =
  map f (iterate f x)               ≡⟨ mapCong₂ (iterate-eq f x) ⟩
  map f (x ∷ iterate f (f · x))     ≡⟨ map-∷ f x (iterate f (f · x)) ⟩
  f · x ∷ map f (iterate f (f · x)) ∎

map-iterate-Stream₁ : ∀ f x → Stream (map f (iterate f x))
map-iterate-Stream₁ f x = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs

  h : A (map f (iterate f x)) →
      ∃[ x' ]  ∃[ xs' ] map f (iterate f x) ≡ x' ∷ xs' ∧ A xs'
  h _ = f · x , map f (iterate f (f · x)) , unfoldMap f x , refl

map-iterate-Stream₂ : ∀ f x → Stream (iterate f (f · x))
map-iterate-Stream₂ f x = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs

  h : A (iterate f (f · x)) →
      ∃[ x' ] ∃[ xs' ] iterate f (f · x) ≡ x' ∷ xs' ∧ A xs'
  h _ = f · x , iterate f (f · (f · x)) , iterate-eq f (f · x) , refl

-- The map-iterate property.
≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind B h (x , refl , refl)
  where
  -- Based on the relation used by (Giménez and Castéran, 2007).
  B : D → D → Set
  B xs ys = ∃[ y ] xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y)

  h : ∀ {xs ys} → B xs ys →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'
  h {xs} {ys} (y , h) =
    f · y
    , map f (iterate f (f · y))
    , iterate f (f · (f · y))
    , trans (∧-proj₁ h) (unfoldMap f y)
    , trans (∧-proj₂ h) (iterate-eq f (f · y))
    , ((f · y) , refl , refl)
