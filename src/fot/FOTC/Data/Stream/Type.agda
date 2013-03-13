------------------------------------------------------------------------------
-- The FOTC streams type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Stream.

module FOTC.Data.Stream.Type where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- The FOTC streams type (co-inductive predicate for total streams).

-- Functional for the Stream predicate.
-- StreamF : (D → Set) → D → Set
-- StreamF A xs = ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'

-- Stream is the greatest fixed-point of StreamF (by Stream-unf and
-- Stream-coind).

postulate Stream : D → Set

postulate
-- Stream is a post-fixed point of StreamF, i.e.
--
-- Stream ≤ StreamF Stream.
  Stream-unf : ∀ {xs} → Stream xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs'
{-# ATP axiom Stream-unf #-}

-- Stream is the greatest post-fixed point of StreamF, i.e
--
-- ∀ P. P ≤ StreamF P ⇒ P ≤ Stream.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Stream-coind : ∀ (A : D → Set) {xs} →
                 -- A is post-fixed point of StreamF.
                 (A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs') →
                 -- Stream is greater than A.
                 A xs → Stream xs

-- Because a greatest post-fixed point is a fixed-point, then the
-- Stream predicate is also a pre-fixed point of the functional
-- StreamF, i.e.
--
-- StreamF Stream ≤ Stream.
Stream-pre-fixed : ∀ {xs} →
                   (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs') →
                   Stream xs
Stream-pre-fixed {xs} h = Stream-coind A prf h
  where
  A : D → Set
  A ws = ∃[ w' ] ∃[ ws' ] ws ≡ w' ∷ ws' ∧ Stream ws'

  prf : A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  prf (_ , _ , xs≡x'∷xs' , Axs') = _ , _ , xs≡x'∷xs' , Stream-unf Axs'
