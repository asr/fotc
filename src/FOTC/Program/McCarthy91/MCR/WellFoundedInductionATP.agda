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
            (∀ {n} → N n → (∀ {m} → N m → MCR m n → P m) → P n) →
            ∀ {n} → N n → P n
wfInd-MCR P accH Nn = accH Nn (helper Nn)
  where
    helper : ∀ {n m} → N n → N m → MCR m n → P m
    helper Nn zN 0«n = ⊥-elim (0«x→⊥ Nn 0«n)

    -- This equation does not pass the termination check.
    helper zN (sN Nm) Sm«0 = accH (sN Nm)
      (λ {m'} Nm' m'«Sm →
        let m'«0 : MCR m' zero
            m'«0 = «-trans Nm' (sN Nm) zN m'«Sm Sm«0

        in helper zN Nm' m'«0
      )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper zN (sN {m} Nm) Sm«0 = accH (sN Nm)
    --   (λ {m'} Nm' m'«Sm →
    --     let m'«m : MCR m' m
    --         m'«m = x«Sy→x«y Nm' Nm m'«Sm

    --     in helper Nm Nm' m'«m
    --   )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper zN Nm m«0 = accH Nm
    --   (λ {m'} Nm' m'«m →
    --     let m'«0 : MCR m' zero
    --         m'«0 = «-trans Nm' Nm zN m'«m m«0

    --     in helper zN Nm' m'«0
    --   )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper {m = m} zN Nm m«0 =
    --   accH Nm (λ {m'} Nm' m'«m → helper Nm Nm' m'«m)

    helper (sN {n} Nn) (sN {m} Nm) Sm«Sn = helper Nn (sN Nm) Sm«n
      where
        Sm«n : MCR (succ m) n
        Sm«n = x«Sy→x«y (sN Nm) Nn Sm«Sn
