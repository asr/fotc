------------------------------------------------------------------------------
-- Bisimilarity relation on unbounded lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity where

open import FOTC.Base
open import FOTC.Base.List

-- We add 3 to the fixities of the standard library.
infix 7 _≈_ _≉_

------------------------------------------------------------------------------
-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- fixed-point (by ≈-unf and ≈-coind) of the bisimulation functional
-- (FOTC.Relation.Binary.Bisimulation).

-- The bisimilarity relation on unbounded lists.
postulate _≈_ : D → D → Set

-- The bisimilarity relation _≈_ on unbounded lists is a post-fixed
-- point of the bisimulation functional (FOTC.Relation.Binary.Bisimulation).
postulate
  ≈-unf : ∀ {xs ys} → xs ≈ ys →
          ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys'
{-# ATP axiom ≈-unf #-}

-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- post-fixed point of the bisimulation functional (see
-- FOTC.Relation.Binary.Bisimulation).
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  ≈-coind : ∀ (B : D → D → Set) {xs ys} →
            -- B is a post-fixed point of the bisimulation functional.
            (B xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
              xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys') →
            -- _≈_ is greater than B.
            B xs ys → xs ≈ ys

------------------------------------------------------------------------------
-- Auxiliary definition.
_≉_ : D → D → Set
x ≉ y = ¬ x ≈ y
{-# ATP definition _≉_ #-}
