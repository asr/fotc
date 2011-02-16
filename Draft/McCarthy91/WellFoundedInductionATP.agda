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

-- Adapted from LTC.Data.Nat.Induction.WellFoundedI.wfInd-LT₁
wfInd-MCR : (P : D → Set) →
            (∀ {m} → N m → (∀ {n} → N n → MCR n m → P n) → P m) →
            ∀ {n} → N n → P n
wfInd-MCR P accH Nn = accH Nn (helper Nn)
  where
    helper : ∀ {m n} → N m → N n → MCR n m → P n
    helper Nm zN 0«m = ⊥-elim (0«x→⊥ Nm 0«m)

    -- This equation does not pass the termination check.
    helper zN (sN Nn) Sn«0 = accH (sN Nn)
      (λ {n'} Nn' n'«Sn →
        let n'«0 : MCR n' zero
            n'«0 = «-trans Nn' (sN Nn) zN n'«Sn Sn«0

        in helper zN Nn' n'«0
      )

    helper (sN {m} Nm) (sN {n} Nn) Sn«Sm = accH (sN Nn)
      (λ {n'} Nn' n'«Sn →
        let n«m : MCR n m
            n«m = Sx«Sy→x«y Nn Nm Sn«Sm

            n'«n : MCR n' n
            n'«n = x«Sy→x«y Nn' Nn n'«Sn

            n'«m : MCR n' m
            n'«m = «-trans Nn' Nn Nm n'«n n«m

        in  helper Nm Nn' n'«m
      )
