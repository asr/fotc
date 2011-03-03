------------------------------------------------------------------------------
-- Well-founded induction on the relation MCR
------------------------------------------------------------------------------

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.McCarthy91.MCR.Induction.Acc.WellFoundedInductionATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.Acc.WellFounded
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers

open import FOTC.Program.McCarthy91.MCR
open import FOTC.Program.McCarthy91.MCR.PropertiesATP

-- Parametrized modules

import FOTC.Data.Nat.Induction.Acc.WellFoundedInduction
open module WF-LT =
  FOTC.Data.Nat.Induction.Acc.WellFoundedInduction.WF₂-LT
  x<0→⊥ x≤y→x<y∨x≡y x<Sy→x≤y

open module II = FOTC.Data.Nat.Induction.Acc.WellFounded.InverseImage fnMCR-N

------------------------------------------------------------------------------
-- The relation MCR is well-founded.
wf-MCR : WellFounded MCR
wf-MCR Nn = wellFounded wf-LT Nn

-- Well-founded induction on the relation MCR.
wfInd-MCR : (P : D → Set) →
            (∀ {n} → N n → (∀ {m} → N m → MCR m n → P m) → P n) →
            ∀ {n} → N n → P n
wfInd-MCR P = WellFoundedInduction wf-MCR
