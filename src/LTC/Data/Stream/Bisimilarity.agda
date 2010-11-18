------------------------------------------------------------------------------
-- Bisimilarity relation on LTC streams
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimilarity where

open import LTC.Base

infix 7 _≈_

------------------------------------------------------------------------------
-- Because the LTC is a first-order theory, we define a first-order
-- version of the bisimilarity relation.

-- The bisimilarity relation.
postulate
  _≈_ : D → D → Set

-- The bisimilarity relation is a post-fixed point of a bisimilar
-- relation BISI (see below).
postulate
  -≈-gfp₁ : {xs ys : D} → xs ≈ ys →
            ∃D (λ x' →
            ∃D (λ xs' →
            ∃D (λ ys' → xs' ≈ ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))
{-# ATP axiom -≈-gfp₁ #-}

-- The bisimilarity relation is the greatest post-fixed point of a
-- bisimilar relation BISI (see below).

-- N.B. This is a second-order axiom. In the proofs, we *must* use an
-- axiom scheme instead. Therefore, we do not add this postulate as an
-- ATP axiom.
postulate
  -≈-gfp₂ : {_R_ : D → D → Set} →
            -- R is a post-fixed point of BISI.
            ({xs ys : D} → xs R ys →
              ∃D (λ x' →
              ∃D (λ xs' →
              ∃D (λ ys' → xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))) →
            -- ≈ is greater than R.
           {xs ys : D} → xs R ys → xs ≈ ys

module Bisimulation where
  -- In LTC we won't use the bisimilar relation BISI. This module is
  -- only for illustrative purposes.

  -- Adapted from [1]. In this paper the authors use the name
  -- 'as (R :: R') bs' (p. 310).
  -- N.B. This definition should work on streams.

  -- [1] Peter Dybjer and Herbert Sander. A functional programming
  -- approach to the specification and verification of concurrent
  -- systems. Formal Aspects of Computing, 1:303–319, 1989.

  -- The bisimilar relation.
  BISI : (D → D → Set) → D → D → Set
  BISI _R_ xs ys =
    ∃D (λ x' →
    ∃D (λ xs' →
    ∃D (λ ys' →
       xs' R ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys')))

  -- The bisimilarity relation is a post-fixed point of BISI.
  -≈→BISI≈ : {xs ys : D} → xs ≈ ys → BISI _≈_ xs ys
  -≈→BISI≈ = -≈-gfp₁

  -- The bisimilarity relation is the greatest post-fixed point of BISI.
  R→BISI-R→R→≈ : {_R_ : D → D → Set} →
                 -- R is a post-fixed point of BISI.
                 ({xs ys : D} → xs R ys → BISI _R_ xs ys) →
                 -- ≈ is greater than R.
                 {xs ys : D} → xs R ys → xs ≈ ys
  R→BISI-R→R→≈ = -≈-gfp₂
