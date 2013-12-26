------------------------------------------------------------------------------
-- The FOTC co-inductive lists type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Colist.

module FOTC.Data.Colist.Type where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- The FOTC co-lists type (co-inductive predicate for total list).

-- Functional for the Colist predicate.
-- ColistF : (D → Set) → D → Set
-- ColistF A xs = xs ≡ [] ∨ ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'

-- Colist is the greatest fixed-point of ColistF (by Colist-unf and
-- Colist-coind).

postulate
  Colist : D → Set

postulate
-- Colist is a post-fixed point of ColistF, i.e.
--
-- Colist ≤ ColistF Colist.
  Colist-unf : ∀ {xs} → Colist xs →
               xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')
{-# ATP axiom Colist-unf #-}

-- Colist is the greatest post-fixed point of ColistF, i.e
--
-- ∀ A. A ≤ ColistF A ⇒ A ≤ Colist.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Colist-coind :
    (A : D → Set) →
    -- A is post-fixed point of ColistF.
    (∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')) →
    -- Colist is greater than A.
    ∀ {xs} → A xs → Colist xs
