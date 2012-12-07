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

-- Functional for the ConatF predicate.
-- ConatF : (D → Set) → D → Set
-- ConatF P n = n = zero ∨ (∃[ n' ] P n' ∧ n = succ n')

-- Conat is the greatest fixed-point of ConatF (by Conat-unf and
-- Conat-coind).

postulate Conat : D → Set

-- Conat is a post-fixed point of ConatF, i.e.
--
-- Conat ≤ ConatF Stream.
postulate
  Conat-unf : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] Conat n' ∧ n ≡ succ₁ n')
{-# ATP axiom Conat-unf #-}

-- Conat is the greatest post-fixed point of ConatF, i.e
--
-- ∀ P. P ≤ ConatF P ⇒ P ≤ Conat.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Conat-coind : (A : D → Set) →
                -- A is post-fixed point of ConatF.
                (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
                -- Conat is greater than A.
                ∀ {n} → A n → Conat n

-- Because a greatest post-fixed point is a fixed-point, then the
-- Conat predicate is also a pre-fixed point of the functional ConatF,
-- i.e,
--
-- ConatF Conat ≤ Conat.
Conat-gfp₃ : ∀ {n} →
             (n ≡ zero ∨ (∃[ n' ] Conat n' ∧ n ≡ succ₁ n')) →
             Conat n
Conat-gfp₃ h = Conat-coind A helper h
  where
  A : D → Set
  A m = m ≡ zero ∨ (∃[ m' ] Conat m' ∧ m ≡ succ₁ m')

  helper : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')
  helper (inj₁ n≡0) = inj₁ n≡0
  helper (inj₂ (n' , CNn' , n≡Sn')) = inj₂ (n' , Conat-unf CNn' , n≡Sn')
