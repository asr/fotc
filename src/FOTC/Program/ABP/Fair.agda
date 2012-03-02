------------------------------------------------------------------------------
-- Fairness of the ABP channels
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Fair where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- The Fair co-inductive predicate

-- From Dybjer and Sander's paper: al : F*T if al is a list of zero or
-- more 0's followed by a final 1.
data F*T : D → Set where
  nilF*T  :                   F*T (T ∷ [])
  consF*T : ∀ {ft} → F*T ft → F*T (F ∷ ft)

-- Functor for the Fair type.
-- FairF : (D → Set) → D → Set
-- FairF X fs = ∃[ ft ] ∃[ fs' ] F*T ft ∧ X fs' ∧ fs ≡ ft ++ fs'

-- Fair is the greatest post-fixed of FairF (by Fair-gfp₁ and Fair-gfp₂).

postulate Fair : D → Set

-- Fair is post-fixed point of FairF (d ≤ f d).
postulate
  Fair-gfp₁ : ∀ {fs} → Fair fs →
              ∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs'
{-# ATP axiom Fair-gfp₁ #-}

-- ∀ e. e ≤ f e => e ≤ d.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Fair-gfp₂ : (P : D → Set) →
              -- P is post-fixed point of FairF.
              (∀ {fs} → P fs →
               ∃[ ft ] ∃[ fs' ] F*T ft ∧ P fs' ∧ fs ≡ ft ++ fs') →
              -- Fair is greater than P.
              ∀ {fs} → P fs → Fair fs

-- Because a greatest post-fixed point is a fixed point, then the Fair
-- predicate is also a pre-fixed point of the functor FairF (f d ≤ d).
Fair-gfp₃ : ∀ {fs} →
            (∃[ ft ] ∃[ fs' ] F*T ft ∧ Fair fs' ∧ fs ≡ ft ++ fs') →
            Fair fs
Fair-gfp₃ h = Fair-gfp₂ P helper h
  where
  P : D → Set
  P ws = ∃[ wl ] ∃[ ws' ] F*T wl ∧ Fair ws' ∧ ws ≡ wl ++ ws'

  helper : ∀ {fs} → P fs → ∃[ ft ] ∃[ fs' ] F*T ft ∧ P fs' ∧ fs ≡ ft ++ fs'
  helper (∃-intro (∃-intro (FTft , Ffs' , h))) =
    ∃-intro (∃-intro (FTft , Fair-gfp₁ Ffs' , h))
