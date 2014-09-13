------------------------------------------------------------------------------
-- Fairness of the ABP channels
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.ABP.Fair.Type where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- The Fair co-inductive predicate

-- From (Dybjer and Sander 1989): al : F*T if al is a list of zero or
-- more 0's followed by a final 1.
data F*T : D → Set where
  f*tnil  : F*T (T ∷ [])
  f*tcons : ∀ {ft} → F*T ft → F*T (F ∷ ft)

-- Functor for the Fair type.
-- FairF : (D → Set) → D → Set
-- FairF A os = ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ A os'

-- Fair is the greatest fixed of FairF (by Fair-out and Fair-coind).

postulate Fair : D → Set

-- Fair a is post-fixed point of FairF, i.e.
--
-- Fair ≤ FairF Fair.
postulate Fair-out : ∀ {os} → Fair os →
                     ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ Fair os'
{-# ATP axiom Fair-out #-}

-- Fair is the greatest post-fixed point of FairF, i.e.
--
-- ∀ A. A ≤ FairF A ⇒ A ≤ Fair.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Fair-coind :
    (A : D → Set) →
    -- A is post-fixed point of FairF.
    (∀ {os} → A os → ∃[ ft ] ∃[ os' ] F*T ft ∧ os ≡ ft ++ os' ∧ A os') →
    -- Fair is greater than A.
    ∀ {os} → A os → Fair os

------------------------------------------------------------------------------
-- References
--
-- Dybjer, Peter and Sander, Herbert P. (1989). A Functional
-- Programming Approach to the Specification and Verification of
-- Concurrent Systems. Formal Aspects of Computing 1, pp. 303–319.
