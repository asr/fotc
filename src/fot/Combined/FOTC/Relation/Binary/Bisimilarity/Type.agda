------------------------------------------------------------------------------
-- Bisimilarity relation on unbounded lists
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Relation.Binary.Bisimilarity.Type where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List

infix 4 _≈_ _≉_

------------------------------------------------------------------------------
-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- fixed-point (by ≈-out and ≈-coind) of the bisimulation functional
-- (Combined.FOTC.Relation.Binary.Bisimulation).

-- The bisimilarity relation on unbounded lists.
postulate _≈_ : D → D → Set

-- The bisimilarity relation _≈_ on unbounded lists is a post-fixed
-- point of the bisimulation functional (Combined.FOTC.Relation.Binary.Bisimulation).
postulate
  ≈-out : ∀ {xs ys} → xs ≈ ys →
          ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys'
{-# ATP axiom ≈-out #-}

-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- post-fixed point of the bisimulation functional (see
-- Combined.FOTC.Relation.Binary.Bisimulation).
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  ≈-coind :
    (B : D → D → Set) →
    -- B is a post-fixed point of the bisimulation functional.
    (∀ {xs ys} → B xs ys →
      ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys') →
    -- _≈_ is greater than B.
    ∀ {xs ys} → B xs ys → xs ≈ ys

------------------------------------------------------------------------------
-- Auxiliary definition.
_≉_ : D → D → Set
x ≉ y = ¬ x ≈ y
{-# ATP definition _≉_ #-}
