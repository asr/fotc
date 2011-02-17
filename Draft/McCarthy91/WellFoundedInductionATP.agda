----------------------------------------------------------------------------
-- Well-founded induction on the relation MCR
----------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module Draft.McCarthy91.WellFoundedInductionATP where

open import LTC.Base

open import Draft.McCarthy91.McCarthy91
open import Draft.McCarthy91.RelationATP

open import LTC.Data.Nat

----------------------------------------------------------------------------

-- Adapted from LTC.Data.Nat.Induction.WellFoundedI.wfInd-LT₁.
wfInd-MCR : (P : D → Set) →
            (∀ {m} → N m → (∀ {n} → N n → MCR n m → P n) → P m) →
            ∀ {n} → N n → P n
wfInd-MCR P accH Nn = accH Nn (helper Nn)
  where
    helper : ∀ {m n} → N m → N n → MCR n m → P n
    helper Nm zN 0«m = ⊥-elim (0«x→⊥ Nm 0«m)

    -- This equation does not pass the termination check.
    helper zN Nn n«0 = accH Nn
      (λ {n'} Nn' n'«n →
        let n'«0 : MCR n' zero
            n'«0 = «-trans Nn' Nn zN n'«n n«0

        in helper zN Nn' n'«0
      )

    helper (sN {m} Nm) (sN {n} Nn) Sn«Sm = helper Nm (sN Nn) Sn«m
      where
        Sn«m : MCR (succ n) m
        Sn«m = x«Sy→x«y (sN Nn) Nm Sn«Sm
