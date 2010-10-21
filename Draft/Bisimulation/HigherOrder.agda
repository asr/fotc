------------------------------------------------------------------------------
-- Bisimulation on LTC streams (higher-order version)
------------------------------------------------------------------------------

module Draft.Bisimulation.HigherOrder where

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

postulate
  GFP     : ((D → D → Set) → D → D → Set) → D → D → Set
  GFP-eq₁ : (f : (D → D → Set) → D → D → Set) → (xs ys : D) →
            GFP f xs ys → f (GFP f) xs ys
  GFP-eq₂ : (f : (D → D → Set) → D → D → Set) → (xs ys : D) →
            f (GFP f) xs ys → GFP f xs ys

-- The bisimilar relation is the (higher-order) greatest fixed-point of
-- the bisimulation relation.
_≈_ : D → D → Set
_≈_ = GFP BISI
