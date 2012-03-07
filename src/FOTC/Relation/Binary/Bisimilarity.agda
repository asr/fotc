------------------------------------------------------------------------------
-- Bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infix 7 _≈_

------------------------------------------------------------------------------
-- The bisimilarity relation _≈_ is the greatest fixed point (by
-- ≈-gfp₁ and ≈-gfp₂) of the bisimulation functional (see below).

-- The bisimilarity relation.
postulate
  _≈_ : D → D → Set

-- The bisimilarity relation _≈_ is a post-fixed point of the
-- bisimulation functional (see below).
postulate
  ≈-gfp₁ : ∀ {xs ys} → xs ≈ ys →
           ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
{-# ATP axiom ≈-gfp₁ #-}

-- The bisimilarity relation _≈_ is the greatest post-fixed point of
-- the bisimulation functional (see below).
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  ≈-gfp₂ : (_R_ : D → D → Set) →
           -- R is a post-fixed point of the bisimulation functional.
           (∀ {xs ys} → xs R ys →
            ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
            xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys') →
           -- _≈_ is greater than R.
           ∀ {xs ys} → xs R ys → xs ≈ ys

-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ is also a pre-fixed point of the
-- bisimulation functional (see below).
≈-gfp₃ : ∀ {xs ys} →
         (∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
          xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys') →
         xs ≈ ys
≈-gfp₃ h = ≈-gfp₂ _R_ helper h
  where
  _R_ : D → D → Set
  _R_ xs ys = ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'

  helper : ∀ {xs ys} → xs R ys →
           ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  helper (_ , _ , _ , xs'≈ys' , prf) = _ , _ , _ , ≈-gfp₁ xs'≈ys' , prf

private
  module Bisimulation where
  -- In FOTC we won't use the bisimulation functional. This module is
  -- only for illustrative purposes.

  -- References:
  --
  -- • Peter Dybjer and Herbert Sander. A functional programming
  --   approach to the specification and verification of concurrent
  --   systems. Formal Aspects of Computing, 1:303–319, 1989.

  -- • Bart Jacobs and Jan Rutten. (Co)algebras and
  --   (co)induction. EATCS Bulletin, 62:222–259, 1997.

  ----------------------------------------------------------------------------
  -- Adapted from (Dybjer and Sander, 1989, p. 310). In this paper, the
  -- authors use the name

  -- as (R :: R') bs'

  -- for the bisimulation functional.

  -- The bisimilarity relation _≈_ is the greatest post-fixed point of
  -- Bisimulation (by post-fp and gpfp).

  -- The bisimulation functional (Jacobs and Rutten, 1997, p. 30).
  Bisimulation : (D → D → Set) → D → D → Set
  Bisimulation _R_ xs ys =
    ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'

  -- The bisimilarity relation _≈_ is a post-fixed point of
  -- Bisimulation, i.e,
  --
  -- _≈_ ≤ Bisimulation _≈_.
  post-fp : ∀ {xs ys} → xs ≈ ys → Bisimulation _≈_ xs ys
  post-fp = ≈-gfp₁

  -- The bisimilarity relation _≈_ is the greatest post-fixed point of
  -- Bisimulation, i.e
  --
  -- ∀ R. R ≤ Bisimulation R ⇒ R ≤ _≈_.
  gpfp : (_R_ : D → D → Set) →
         -- R is a post-fixed point of Bisimulation.
         (∀ {xs ys} → xs R ys → Bisimulation _R_ xs ys) →
         -- _≈_ is greater than R.
         ∀ {xs ys} → xs R ys → xs ≈ ys
  gpfp = ≈-gfp₂

  -- Because a greatest post-fixed point is a fixed-point, the
  -- bisimilarity relation _≈_ is also a pre-fixed point of
  -- Bisimulation, i.e.
  --
  -- Bisimulation _≈_ ≤ _≈_.
  pre-fp : ∀ {xs ys} → Bisimulation _≈_ xs ys → xs ≈ ys
  pre-fp = ≈-gfp₃
