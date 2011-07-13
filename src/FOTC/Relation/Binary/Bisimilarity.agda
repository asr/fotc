------------------------------------------------------------------------------
-- Bisimilarity relation on FOTC
------------------------------------------------------------------------------

module FOTC.Relation.Binary.Bisimilarity where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infix 7 _≈_

------------------------------------------------------------------------------
-- The bisimilarity relation.
postulate
  _≈_ : D → D → Set

-- The bisimilarity relation is a post-fixed point of the functor
-- BisimilarityF (see below).
postulate
  ≈-gfp₁ : ∀ {xs ys} → xs ≈ ys →
           ∃ λ x' → ∃ λ xs' → ∃ λ ys' → xs' ≈ ys' ∧
                                        xs ≡ x' ∷ xs' ∧
                                        ys ≡ x' ∷ ys'
{-# ATP axiom ≈-gfp₁ #-}

-- The bisimilarity relation is the greatest post-fixed point of the
-- functor BisimilarityF (see below).

-- N.B. This is a second-order axiom. In the automatic proofs, we
-- *must* use an instance. Therefore, we do not add this postulate as
-- an ATP axiom.
postulate
  ≈-gfp₂ : (_R_ : D → D → Set) →
           -- R is a post-fixed point of BisimilarityF.
           (∀ {xs ys} → xs R ys →
            ∃ λ x' → ∃ λ xs' → ∃ λ ys' → xs' R ys' ∧
                                         xs ≡ x' ∷ xs' ∧
                                         ys ≡ x' ∷ ys') →
           -- _≈_ is greater than R.
           ∀ {xs ys} → xs R ys → xs ≈ ys

module BisimilarityF where
  -- In FOTC we won't use the bisimilarity functor. This module is
  -- only for illustrative purposes.

  -- Adapted from [1]. In this paper the authors use the name
  -- 'as (R :: R') bs' (p. 310) for the functor BisimilarityF.

  -- [1] Peter Dybjer and Herbert Sander. A functional programming
  -- approach to the specification and verification of concurrent
  -- systems. Formal Aspects of Computing, 1:303–319, 1989.

  -- The bisimilarity functor.
  BisimilarityF : (D → D → Set) → D → D → Set
  BisimilarityF _R_ xs ys =
    ∃ λ x' → ∃ λ xs' → ∃ λ ys' → xs' R ys' ∧
                                 xs ≡ x' ∷ xs' ∧
                                 ys ≡ x' ∷ ys'

  -- The bisimilarity relation is a post-fixed point of BisimilarityF.
  pfp : ∀ {xs ys} → xs ≈ ys → BisimilarityF _≈_ xs ys
  pfp = ≈-gfp₁

  -- The bisimilarity relation is the greatest post-fixed point of
  -- BisimilarityF.
  gpfp : (_R_ : D → D → Set) →
         -- R is a post-fixed point of BisimilarityF.
         (∀ {xs ys} → xs R ys → BisimilarityF _R_ xs ys) →
         -- _≈_ is greater than R.
         ∀ {xs ys} → xs R ys → xs ≈ ys
  gpfp = ≈-gfp₂
