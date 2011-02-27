----------------------------------------------------------------------------
-- Well-founded induction on the relation MCR
----------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.McCarthy91.MCR.WellFoundedInductionATP where

open import FOTC.Base

open import FOTC.Data.Nat

open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.MCR
open import FOTC.Program.McCarthy91.MCR.PropertiesATP

----------------------------------------------------------------------------

-- Adapted from FOTC.Data.Nat.Induction.WellFoundedI.wfInd-LT₁.
wfInd-MCR : (P : D → Set) →
            (∀ {m} → N m → (∀ {n} → N n → MCR n m → P n) → P m) →
            ∀ {n} → N n → P n
wfInd-MCR P accH Nn = accH Nn (helper Nn)
  where
    helper : ∀ {m n} → N m → N n → MCR n m → P n
    helper Nm zN 0«m = ⊥-elim (0«x→⊥ Nm 0«m)

    -- This equation does not pass the termination check.
    helper zN (sN {n} Nn) Sn«0 = accH (sN Nn)
      (λ {n'} Nn' n'«Sn →
        let n'«0 : MCR n' zero
            n'«0 = «-trans Nn' (sN Nn) zN n'«Sn Sn«0

        in helper zN Nn' n'«0
      )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper zN (sN {n} Nn) Sn«0 = accH (sN Nn)
    --   (λ {n'} Nn' n'«Sn →
    --     let n'«n : MCR n' n
    --         n'«n = x«Sy→x«y Nn' Nn n'«Sn

    --     in helper Nn Nn' n'«n
    --   )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper zN Nn n«0 = accH Nn
    --   (λ {n'} Nn' n'«n →
    --     let n'«0 : MCR n' zero
    --         n'«0 = «-trans Nn' Nn zN n'«n n«0

    --     in helper zN Nn' n'«0
    --   )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper {n = n} zN Nn n«0 =
    --   accH Nn (λ {n'} Nn' n'«n → helper Nn Nn' n'«n)

    helper (sN {m} Nm) (sN {n} Nn) Sn«Sm = helper Nm (sN Nn) Sn«m
      where
        Sn«m : MCR (succ n) m
        Sn«m = x«Sy→x«y (sN Nn) Nm Sn«Sm
