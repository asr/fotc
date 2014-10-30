------------------------------------------------------------------------------
-- The FOTC co-inductive natural numbers type
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B. This module is re-exported by FOTC.Data.Conat.

-- Adapted from (Sander 1992).

module FOTC.Data.Conat.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC co-inductive natural numbers type (co-inductive predicate
-- for total co-inductive natural)

-- Functional for the NatF predicate.
-- NatF : (D → Set) → D → Set
-- NatF A n = n = zero ∨ (∃[ n' ] n = succ n' ∧ A n')

-- Conat is the greatest fixed-point of NatF (by Conat-out and
-- Conat-coind).

postulate Conat : D → Set

-- Conat is a post-fixed point of NatF, i.e.
--
-- Conat ≤ NatF Conat.
postulate
  Conat-out : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
{-# ATP axiom Conat-out #-}

-- Conat is the greatest post-fixed point of NatF, i.e.
--
-- ∀ A. A ≤ NatF A ⇒ A ≤ Conat.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Conat-coind :
    (A : D → Set) →
    -- A is post-fixed point of NatF.
    (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
    -- Conat is greater than A.
    ∀ {n} → A n → Conat n

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
