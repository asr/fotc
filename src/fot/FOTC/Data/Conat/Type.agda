------------------------------------------------------------------------------
-- The FOTC co-inductive natural numbers type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Conat.

-- Adapted from (Sander 1992).

-- References:
--
-- • Herbert P. Sander. A logic of functional programs with an
--   application to concurrency. PhD thesis, Chalmers University of
--   Technology and University of Gothenburg, Department of Computer
--   Sciences, 1992.

module FOTC.Data.Conat.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC co-inductive natural numbers type (co-inductive predicate
-- for total co-inductive natural)

-- Functional for the NatF predicate.
-- NatF : (D → Set) → D → Set
-- NatF A n = n = zero ∨ (∃[ n' ] n = succ n' ∧ P n')

-- Conat is the greatest fixed-point of NatF (by Conat-unf and
-- Conat-coind).

postulate Conat : D → Set

-- Conat is a post-fixed point of NatF, i.e.
--
-- Conat ≤ NatF Conat.
postulate
  Conat-unf : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
{-# ATP axiom Conat-unf #-}

-- Conat is the greatest post-fixed point of NatF, i.e
--
-- ∀ P. P ≤ NatF P ⇒ P ≤ Conat.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Conat-coind : ∀ (A : D → Set) {n} →
                -- A is post-fixed point of NatF.
                (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
                -- Conat is greater than A.
                A n → Conat n

-- Because a greatest post-fixed point is a fixed-point, then the
-- Conat predicate is also a pre-fixed point of the functional NatF,
-- i.e,
--
-- NatF Conat ≤ Conat.
Conat-pre-fixed : ∀ {n} →
                  (n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')) →
                  Conat n
Conat-pre-fixed {n} h = Conat-coind A prf h
  where
  A : D → Set
  A m = m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ Conat m')

  prf : A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  prf (inj₁ n≡0) = inj₁ n≡0
  prf (inj₂ (n' , n≡Sn' , An')) = inj₂ (n' , n≡Sn' , Conat-unf An')
