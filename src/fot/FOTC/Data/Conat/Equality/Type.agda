------------------------------------------------------------------------------
-- Equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.Equality.Type where

open import FOTC.Base

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/Stream.agda).
infix 7 _≈_

------------------------------------------------------------------------------
-- Functional for the relation _≈_ (adapted from (Sander 1992,
-- p. 58)).
--
-- ≈-F : (D → D → Set) → D → D → Set
-- ≈-F R m n =
-- (m ≡ zero ∧ n ≡ zero) ∨ (∃[ m' ] ∃[ n' ] m ≡ succ m' ∧ n ≡ succ n' ∧ R m' n')

-- The relation _≈_ is the greatest post-fixed point of the functional
-- ≈-F (by ≈-out and ≈-coind).

-- The equality on Conat.
postulate _≈_ : D → D → Set

-- The relation _≈_ is a post-fixed point of the functional ≈-F,
-- i.e.
--
-- _≈_ ≤ ≈-F _≈_.
postulate ≈-out : ∀ {m n} → m ≈ n →
                  m ≡ zero ∧ n ≡ zero
                  ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈ n')
{-# ATP axiom ≈-out #-}

-- The relation _N≈_ is the greatest post-fixed point of _N≈_, i.e.
--
-- ∀ R. R ≤ ≈-F R ⇒ R ≤ _N≈_.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  ≈-coind :
    (R : D → D → Set) →
    -- R is a post-fixed point of the functional ≈-F.
    (∀ {m n} → R m n → m ≡ zero ∧ n ≡ zero
      ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')) →
    -- _≈_ is greater than R.
    ∀ {m n} → R m n → m ≈ n

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
