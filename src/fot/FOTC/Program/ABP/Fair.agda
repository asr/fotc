------------------------------------------------------------------------------
-- Fairness of the ABP channels
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Peter Dybjer and Herbert Sander. A functional programming
--   approach to the specification and verification of concurrent
--   systems. Formal Aspects of Computing, 1:303–319, 1989.

module FOTC.Program.ABP.Fair where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- The Fair co-inductive predicate

-- From (Dybjer and Sander 1989): al : F*T if al is a list of zero or
-- more 0's followed by a final 1.
data F*T : D → Set where
  f*tnil  :                   F*T (T ∷ [])
  f*tcons : ∀ {ft} → F*T ft → F*T (F ∷ ft)

-- Functor for the Fair type.
-- FairF : (D → Set) → D → Set
-- FairF X fs = ∃[ ft ] ∃[ fs' ] F*T ft ∧ X fs' ∧ fs ≡ ft ++ fs'

-- Fair is the greatest fixed of FairF (by Fair-unf and Fair-coind).

postulate Fair : D → Set

-- Fair a is post-fixed point of FairF, i.e.
--
-- Fair ≤ FairF Fair.
postulate Fair-unf : ∀ {fs} → Fair fs →
                     ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs'
{-# ATP axiom Fair-unf #-}

-- Fair is the greatest post-fixed point of FairF, i.e
--
-- ∀ P. P ≤ FairF P ⇒ P ≤ Fair.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate Fair-coind : (A : D → Set) →
                       -- A is post-fixed point of FairF.
                       (∀ {fs} → A fs →
                         ∃[ ft ] ∃[ fs' ] F*T ft ∧ A fs' ∧ fs ≡ ft ++ fs') →
                       -- Fair is greater than A.
                       ∀ {fs} → A fs → Fair fs

-- Because a greatest post-fixed point is a fixed-point, then the Fair
-- predicate is also a pre-fixed point of the functional FairF, i.e.
--
-- FairF Fair ≤ Fair.
Fair-gfp₃ : ∀ {fs} →
            (∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs') →
            Fair fs
Fair-gfp₃ h = Fair-coind A helper h
  where
  A : D → Set
  A ws = ∃[ wl ] ∃[ ws' ] F*T wl ∧ Fair ws' ∧ ws ≡ wl ++ ws'

  helper : ∀ {fs} → A fs → ∃[ ft ] ∃[ fs' ] F*T ft ∧ A fs' ∧ fs ≡ ft ++ fs'
  helper (_ , _ , FTft , Ffs' , h) = _ , _ , FTft , Fair-unf Ffs' , h
