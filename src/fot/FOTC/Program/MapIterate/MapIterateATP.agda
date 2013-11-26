------------------------------------------------------------------------------
-- The map-iterate property: A property using coinduction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property (Gibbons and Hutton 2005):
-- map f (iterate f x) = iterate f (f · x)

-- References:
--
-- • Giménez, Eduardo and Casterán, Pierre (2007). A Tutorial on
--   [Co-]Inductive Types in Coq.
--
-- • Gibbons, Jeremy and Hutton, Graham (2005). Proof Methods for
--   Corecursive Programs. In: Fundamenta Informaticae XX, pp. 1–14.

module FOTC.Program.MapIterate.MapIterateATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

map-iterate-Stream₁ : ∀ f x → Stream (map f (iterate f x))
map-iterate-Stream₁ f x = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs
  {-# ATP definition A #-}

  postulate
    h : A (map f (iterate f x)) →
        ∃[ x' ]  ∃[ xs' ] map f (iterate f x) ≡ x' ∷ xs' ∧ A xs'
  {-# ATP prove h #-}

map-iterate-Stream₂ : ∀ f x → Stream (iterate f (f · x))
map-iterate-Stream₂ f x = Stream-coind A h refl
  where
  A : D → Set
  A xs = xs ≡ xs
  {-# ATP definition A #-}

  postulate
    h : A (iterate f (f · x)) →
        ∃[ x' ] ∃[ xs' ] iterate f (f · x) ≡ x' ∷ xs' ∧ A xs'
  {-# ATP prove h #-}

-- The map-iterate property.
≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind B h refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs
  {-# ATP definition B #-}

  postulate
    h : B (map f (iterate f x)) (iterate f (f · x)) →
        ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
          map f (iterate f x) ≡ x' ∷ xs'
          ∧ iterate f (f · x) ≡ x' ∷ ys'
          ∧ B xs' ys'
  {-# ATP prove h #-}
