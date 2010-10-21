------------------------------------------------------------------------------
-- Bisimulation on LTC streams (higher-order version)
------------------------------------------------------------------------------

module LTC.Data.Stream.Bisimulation.HigherOrder where

open import LTC.Minimal
open import LTC.Data.Stream.Bisimulation using ( BISI )

infix 4 _≈_

------------------------------------------------------------------------------

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
