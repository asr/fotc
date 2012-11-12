------------------------------------------------------------------------------
-- Well-founded induction on the relation MCR
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.McCarthy91.MCR.Induction.Acc.WellFoundedInductionATP where

open import FOTC.Base
open import FOTC.Data.Nat

import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionATP
open FOTC.Data.Nat.Induction.Acc.WellFoundedInductionATP.WF-<

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Induction.WellFounded
open import FOTC.Program.McCarthy91.MCR
open import FOTC.Program.McCarthy91.MCR.PropertiesATP

-- Parametrized modules
open module InvImg =
  FOTC.Induction.WellFounded.InverseImage {N} {N} {_<_} fnMCR-N

------------------------------------------------------------------------------
-- The relation MCR is well-founded (using the inverse image combinator).
wf-MCR : WellFounded MCR
wf-MCR Nn = wellFounded wf-< Nn

-- Well-founded induction on the relation MCR.
wfInd-MCR : (A : D → Set) →
            (∀ {n} → N n → (∀ {m} → N m → MCR m n → A m) → A n) →
            ∀ {n} → N n → A n
wfInd-MCR A = WellFoundedInduction wf-MCR
