------------------------------------------------------------------------------
-- Equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Sander, Herbert P. (1992). A Logic of Functional Programs with an
--   Application to Concurrency. PhD thesis. Department of Computer
--   Sciences: Chalmers University of Technology and University of
--   Gothenburg.

module FOTC.Data.Conat.Equality where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infix 7 _≈N_

------------------------------------------------------------------------------
-- Functional for the relation _≈N_ (adapted from (Sander 1992,
-- p. 58)).
--
-- ≈NF : (D → D → Set) → D → D → Set
-- ≈NF R m n =
-- (m ≡ zero ∧ n ≡ zero) ∨ (∃[ m' ] ∃[ n' ] m ≡ succ m' ∧ n ≡ succ n' ∧ R m' n')

-- The relation _≈N_ is the greatest post-fixed point of the
-- functional ≈NF (by ≈N-unf and ≈N-coind).

-- The equality on Conat.
postulate _≈N_ : D → D → Set

-- The relation _≈N_ is a post-fixed point of the functional ≈NF, i.e.
--
-- _≈N_ ≤ ≈NF _≈N_.
postulate ≈N-unf : ∀ {m n} → m ≈N n →
                   m ≡ zero ∧ n ≡ zero
                   ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈N n')
{-# ATP axiom ≈N-unf #-}

-- The relation _N≈_ is the greatest post-fixed point of _N≈_, i.e
--
-- ∀ R. R ≤ ≈NF R ⇒ R ≤ _N≈_.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  ≈N-coind : ∀ (R : D → D → Set) {m n} →
             -- R is a post-fixed point of the functional ≈NF.
             (R m n → m ≡ zero ∧ n ≡ zero
               ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')) →
             -- _≈N_ is greater than R.
             R m n → m ≈N n
