------------------------------------------------------------------------------
-- The FOTC coinductive natural numbers type
------------------------------------------------------------------------------

-- Adapted from: Herbert P. Sander. A logic of functional programs
-- with an application to concurrency. PhD thesis, Chalmers University
-- of Technology and University of Gothenburg, Department of Computer
-- Sciences, 1992.

module FOTC.Data.Conat.Type where

open import FOTC.Base

------------------------------------------------------------------------------

-- Functional for the FOTC coinductive natural numbers type.
-- ConatF : (D → Set) → D → Set
-- ConatF P n = ∃ λ n' → P n' ∧ n = succ n'

postulate
  Conat : D → Set

-- Conat is post-fixed point of ConatF (d ≤ f d).
postulate
  Conat-gfp₁ : ∀ {n} → Conat n → ∃ λ n' → Conat n' ∧ n ≡ succ n'
{-# ATP axiom Conat-gfp₁ #-}

-- Conat is the greatest post-fixed of ConatF
--
-- (If ∀ e. e ≤ f e => e ≤ d, then d is the greatest post-fixed point
-- of f).

-- N.B. This is a second-order axiom. In the automatic proofs, we
-- *must* use an instance. Therefore, we do not add this postulate as
-- an ATP axiom.
postulate
  Conat-gfp₂ : (P : D → Set) →
               -- P is post-fixed point of ConatF.
               (∀ {n} → P n → ∃ λ n' → P n' ∧ n ≡ succ n') →
               -- Conat is greater than P.
               ∀ {n} → P n → Conat n

-- Because a greatest post-fixed point is a fixed point, then the
-- Conat predicate is also a pre-fixed point of the functor ConatF
-- (f d ≤ d).
Conat-gfp₃ : ∀ {n} →
             (∃ λ n' → Conat n' ∧ n ≡ succ n') →
             Conat n
Conat-gfp₃ h = Conat-gfp₂ P helper h
  where
  P : D → Set
  P m = ∃ λ m' → Conat m' ∧ m ≡ succ m'

  helper : ∀ {n} → P n → ∃ λ n' → P n' ∧ n ≡ succ n'
  helper (n' , CNn' , n≡Sn') = n' , (Conat-gfp₁ CNn') , n≡Sn'
