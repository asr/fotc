------------------------------------------------------------------------------
-- The map-iterate property: A property using coinduction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The map-iterate property [1]:
-- map f (iterate f x) = iterate f (f · x)

-- [1] Jeremy Gibbons and Graham Hutton. Proof methods for corecursive
-- programs. Fundamenta Informaticae, XX:1–14, 2005.

module FOTC.Program.MapIterate.MapIterateATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------
-- The map-iterate property.

≈-map-iterate : ∀ f x → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-gfp₂ R helper (∃-intro (refl , refl))
  where
  postulate
    unfoldMap : ∀ f y →
                map f (iterate f y) ≡ f · y ∷ map f (iterate f (f · y))
  {-# ATP prove unfoldMap #-}

  postulate
    unfoldIterate : ∀ f y →
                    iterate f (f · y) ≡ f · y ∷ iterate f (f · (f · y))
  {-# ATP prove unfoldIterate #-}

  -- The relation R was based on the relation used by Eduardo Giménez
  -- and Pierre Castéran. A Tutorial on [Co-]Inductive Types in
  -- Coq. May 1998 -- August 17, 2007.
  R : D → D → Set
  R xs ys = ∃[ y ] xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y)

  -- 2012-02-28. We required the existential witness on a pattern matching.
  helper : ∀ {xs ys} → R xs ys →
           ∃[ x' ] ∃[ xs' ] ∃[ ys' ] R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  helper {xs} {ys} (∃-intro {y} h) =
  -- NB. We write the witness *only* for documentation.
    ∃-intro {x = f · y} $
    ∃-intro {x = map f (iterate f (f · y))} $
    ∃-intro {x = iterate f (f · (f · y))} $
    (∃-intro {x = f · y} (refl , refl)
             , trans xs≡map (unfoldMap f y)
             , trans ys≡iterate (unfoldIterate f y))
    where
    xs≡map : xs ≡ map f (iterate f y)
    xs≡map = ∧-proj₁ h

    ys≡iterate : ys ≡ iterate f (f · y)
    ys≡iterate = ∧-proj₂ h
