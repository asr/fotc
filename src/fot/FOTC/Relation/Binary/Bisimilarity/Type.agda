------------------------------------------------------------------------------
-- Bisimilarity relation on unbounded lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity.Type where

open import FOTC.Base
open import FOTC.Base.List

-- We add 3 to the fixities of the Agda standard library 0.6 (see
-- Data/Stream.agda).
infix 7 _≈_ _≉_

------------------------------------------------------------------------------
-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- fixed-point (by ≈-out and ≈-coind) of the bisimulation functional
-- (FOTC.Relation.Binary.Bisimulation).

-- The bisimilarity relation on unbounded lists.
postulate _≈_ : D → D → Set

-- The bisimilarity relation _≈_ on unbounded lists is a post-fixed
-- point of the bisimulation functional (FOTC.Relation.Binary.Bisimulation).
postulate
  ≈-out : ∀ {xs ys} → xs ≈ ys →
          ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys'
{-# ATP axiom ≈-out #-}

-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- post-fixed point of the bisimulation functional (see
-- FOTC.Relation.Binary.Bisimulation).
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
