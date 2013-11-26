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
-- (see below).

-- The bisimilarity relation on unbounded lists.
postulate _≈_ : D → D → Set

-- The bisimilarity relation _≈_ on unbounded lists is a post-fixed
-- point of the bisimulation functional (see below).
postulate
  ≈-unf : ∀ {xs ys} → xs ≈ ys →
          ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys'
{-# ATP axiom ≈-unf #-}

-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- post-fixed point of the bisimulation functional (see below).
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

-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
-- point of the bisimulation functional (see below).
≈-pre-fixed : ∀ {xs ys} →
              (∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
                xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys') →
              xs ≈ ys
≈-pre-fixed {xs} {ys} h = ≈-coind B h' h
  where
  B : D → D → Set
  B xs ys = ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
              xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys'

  h' : B xs ys →
       ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'
  h' (_ , _ , _ , prf₁ , prf₂ , xs'≈ys') =
    _ , _ , _ , prf₁ , prf₂ , ≈-unf xs'≈ys'

------------------------------------------------------------------------------
-- Auxiliary definition.
_≉_ : D → D → Set
x ≉ y = ¬ x ≈ y
{-# ATP definition _≉_ #-}

------------------------------------------------------------------------------

private
  module Bisimulation where
  -- In FOTC we won't use the bisimulation functional on unbounded
  -- lists. This module is only for illustrative purposes.

  -- References:
  --
  -- • Dybjer, Peter and Sander, Herbert P. (1989). A Functional
  --   Programming Approach to the Speciﬁcation and Veriﬁcation of
  --   Concurrent Systems. In: Formal Aspects of Computing 1,
  --   pp. 303–319.
  --
  -- • Jacobs, Bart and Rutten, Jan (1997). A Tutorial on (Co)Algebras
  --   and (Co)Induction. In: EATCS Bulletin 62, pp. 222–259.

  ----------------------------------------------------------------------------
  -- The bisimilarity relation _≈_ on unbounded lists is the greatest
  -- post-fixed point of Bisimulation (by post-fp and gpfp).

  -- The bisimulation functional on unbounded lists (adapted from
  -- Dybjer and Sander 1989, p. 310, and Jacobs and Rutten 1997,
  -- p. 30).
  BisimulationF : (D → D → Set) → D → D → Set
  BisimulationF B xs ys =
    ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'

  -- The bisimilarity relation _≈_ on unbounded lists is a post-fixed
  -- point of Bisimulation, i.e,
  --
  -- _≈_ ≤ Bisimulation _≈_.
  post-fp : ∀ {xs ys} → xs ≈ ys → BisimulationF _≈_ xs ys
  post-fp = ≈-unf

  -- The bisimilarity relation _≈_ on unbounded lists is the greatest
  -- post-fixed point of Bisimulation, i.e
  --
  -- ∀ B. B ≤ Bisimulation B ⇒ B ≤ _≈_.
  gpfp : ∀ (B : D → D → Set) {xs ys} →
         -- B is a post-fixed point of Bisimulation.
         (B xs ys → BisimulationF B xs ys) →
         -- _≈_ is greater than B.
         B xs ys → xs ≈ ys
  gpfp = ≈-coind

  -- Because a greatest post-fixed point is a fixed-point, the
  -- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
  -- point of Bisimulation, i.e.
  --
  -- Bisimulation _≈_ ≤ _≈_.
  pre-fp : ∀ {xs ys} → BisimulationF _≈_ xs ys → xs ≈ ys
  pre-fp = ≈-pre-fixed
