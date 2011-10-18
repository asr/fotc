------------------------------------------------------------------------------
-- Fairness of the ABP channels
------------------------------------------------------------------------------

module FOTC.Program.ABP.Fair where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- The Fair co-inductive predicate

-- From the paper: al : O*L if al is a list of zero or more O's
-- followed by a final L.
data O*L : D → Set where
  nilO*L  :                 O*L (L ∷ [])
  consO*L : ∀ ol → O*L ol → O*L (O ∷ ol)

-- Functor for the Fair type.
-- FairF : (D → Set) → D → Set
-- FairF X os = ∃ λ ol → ∃ λ os' → O*L ol ∧ X os' ∧ os ≡ ol ++ os'

postulate Fair : D → Set

-- Fair is post-fixed point of FairF (d ≤ f d).
postulate
  Fair-gfp₁ : ∀ {os} → Fair os →
              ∃ λ ol → ∃ λ os' → O*L ol ∧ Fair os' ∧ os ≡ ol ++ os'
{-# ATP axiom Fair-gfp₁ #-}

-- Fair is the greatest post-fixed of FairF.
--
-- (If ∀ e. e ≤ f e => e ≤ d, then d is the greatest post-fixed point
-- of f).

-- N.B. This is a second-order axiom. In the automatic proofs, we
-- *must* use an instance. Therefore, we do not add this postulate as
-- an ATP axiom.
postulate
  Fair-gfp₂ : (P : D → Set) →
              -- P is post-fixed point of FairF.
              (∀ {os} → P os →
               ∃ λ ol → ∃ λ os' → O*L ol ∧ P os' ∧ os ≡ ol ++ os') →
              -- Fair is greater than P.
              ∀ {os} → P os → Fair os

-- Because a greatest post-fixed point is a fixed point, then the Fair
-- predicate is also a pre-fixed point of the functor FairF (f d ≤ d).
Fair-gfp₃ : ∀ {os} →
            (∃ λ ol → ∃ λ os' → O*L ol ∧ Fair os' ∧ os ≡ ol ++ os') →
            Fair os
Fair-gfp₃ h = Fair-gfp₂ P helper h
  where
  P : D → Set
  P ws = ∃ λ wl → ∃ λ ws' → O*L wl ∧ Fair ws' ∧ ws ≡ wl ++ ws'

  helper : {os : D} → P os → ∃ λ ol → ∃ λ os' → O*L ol ∧ P os' ∧ os ≡ ol ++ os'
  helper (ol , os' , OLol , Fos' , h) = ol , os' , OLol , Fair-gfp₁ Fos' , h
