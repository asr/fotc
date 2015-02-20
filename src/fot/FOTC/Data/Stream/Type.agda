------------------------------------------------------------------------------
-- The FOTC streams type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Stream.Type where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- The FOTC streams type (co-inductive predicate for total streams).

-- Functional for the Stream predicate.
-- StreamF : (D → Set) → D → Set
-- StreamF A xs = ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'

-- Stream is the greatest fixed-point of StreamF (by Stream-out and
-- Stream-coind).

postulate Stream : D → Set

postulate
-- Stream is a post-fixed point of StreamF, i.e.
--
-- Stream ≤ StreamF Stream.
  Stream-out : ∀ {xs} → Stream xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs'
{-# ATP axiom Stream-out #-}

-- Stream is the greatest post-fixed point of StreamF, i.e.
--
-- ∀ A. A ≤ StreamF A ⇒ A ≤ Stream.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Stream-coind :
    (A : D → Set) →
    -- A is post-fixed point of StreamF.
    (∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs') →
    -- Stream is greater than A.
    ∀ {xs} → A xs → Stream xs
