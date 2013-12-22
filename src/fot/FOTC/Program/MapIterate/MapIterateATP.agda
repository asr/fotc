------------------------------------------------------------------------------
-- The map-iterate property: A property using coinduction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property (Gibbons and Hutton 2005):
-- map f (iterate f x) = iterate f (f · x)

module FOTC.Program.MapIterate.MapIterateATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

map-iterate-Stream₁ : ∀ f x → Stream (map f (iterate f x))
map-iterate-Stream₁ f x = Stream-coind (λ xs → xs ≡ xs) h refl
  where
  postulate
    h : map f (iterate f x) ≡ map f (iterate f x) →
        ∃[ x' ]  ∃[ xs' ] map f (iterate f x) ≡ x' ∷ xs' ∧ xs' ≡ xs'
  {-# ATP prove h #-}

map-iterate-Stream₂ : ∀ f x → Stream (iterate f (f · x))
map-iterate-Stream₂ f x = Stream-coind (λ xs → xs ≡ xs) h refl
  where
  postulate
    h : iterate f (f · x) ≡ iterate f (f · x) →
        ∃[ x' ] ∃[ xs' ] iterate f (f · x) ≡ x' ∷ xs' ∧ xs' ≡ xs'
  {-# ATP prove h #-}

-- The map-iterate property.
≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-coind (λ xs _ → xs ≡ xs) h refl
  where
  postulate
    h : map f (iterate f x) ≡ map f (iterate f x) →
        ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
          map f (iterate f x) ≡ x' ∷ xs'
          ∧ iterate f (f · x) ≡ x' ∷ ys'
          ∧ xs' ≡ xs'
  {-# ATP prove h #-}

------------------------------------------------------------------------------
-- References
--
-- Gibbons, Jeremy and Hutton, Graham (2005). Proof Methods for
-- Corecursive Programs. In: Fundamenta Informaticae XX, pp. 1–14.
