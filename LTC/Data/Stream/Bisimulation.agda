------------------------------------------------------------------------------
-- Bisimulation on LTC streams
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimulation where

open import LTC.Minimal

infix 4 _≈_

------------------------------------------------------------------------------

-- Adapted from [1]. In this paper the authors use the name
-- 'as (R :: R') bs' (p. 310).
-- N.B. This definition should work on streams.

-- [1] Peter Dybjer and Herbert Sander. A functional programming
-- approach to the specification and verification of concurrent
-- systems. Formal Aspects of Computing, 1:303–319, 1989.
BISI : (D → D → Set) → D → D → Set
BISI R xs ys =
  ∃D (λ x' →
  ∃D (λ y' →
  ∃D (λ xs' →
  ∃D (λ ys' →
     x' ≡ y' ∧ R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ y' ∷ ys'))))

-- Because the LTC is a first-order theory, we define a first-order
-- version of the bisimilar relation.
postulate
  _≈_       : D → D → Set
  ≈-GFP-eq₁ : {xs ys : D} → xs ≈ ys → BISI _≈_ xs ys
  ≈-GFP-eq₂ : {xs ys : D} → BISI _≈_ xs ys → xs ≈ ys
