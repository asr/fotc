------------------------------------------------------------------------------
-- The map-iterate property: A property using coinduction
------------------------------------------------------------------------------

-- The map-iterate property [1]:
-- map f (iterate f x) = iterate f (f · x)

-- [1] Jeremy Gibbons and Graham Hutton. Proof methods for corecursive
-- programs. Fundamenta Informaticae, XX:1–14, 2005.

module FOTC.Program.MapIterate.MapIterateATP where

open import FOTC.Base

open import FOTC.Data.List
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- The map-iterate property.

≈-map-iterate : (f x : D) → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x = ≈-gfp₂ R (λ {xs} {ys} → helper xs ys) (x , refl , refl)
  where
  -- The relation R was based on the relation used by Eduardo Giménez
  -- and Pierre Castéran. A Tutorial on [Co-]Inductive Types in
  -- Coq. May 1998 -- August 17, 2007.
  R : D → D → Set
  R xs ys = ∃ (λ y → xs ≡ map f (iterate f y) ∧ ys ≡ iterate f (f · y))

  helper : ∀ xs ys → R xs ys → ∃ (λ x' → ∃ (λ xs' → ∃ (λ ys' →
             R xs' ys' ∧
             xs ≡ x' ∷ xs' ∧
             ys ≡ x' ∷ ys')))
  helper xs ys h = (f · y)
                   , (map f (iterate f (f · y)))
                   , (iterate f (f · (f · y)))
                   , ((f · y) , refl , refl)
                   , (trans xs≡map unfoldMap)
                   , trans ys≡iterate unfoldIterate
    where
    y : D
    y = ∃-proj₁ h

    xs≡map : xs ≡ map f (iterate f y)
    xs≡map = ∧-proj₁ (∃-proj₂ h)

    ys≡iterate : ys ≡ iterate f (f · y)
    ys≡iterate = ∧-proj₂ (∃-proj₂ h)

    postulate
      unfoldMap : map f (iterate f y) ≡ f · y ∷ map f (iterate f (f · y))
      unfoldIterate : iterate f (f · y) ≡ f · y ∷ iterate f (f · (f · y))
    {-# ATP prove unfoldMap #-}
    {-# ATP prove unfoldIterate #-}
