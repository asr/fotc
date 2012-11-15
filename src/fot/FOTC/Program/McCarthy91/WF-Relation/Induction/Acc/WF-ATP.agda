------------------------------------------------------------------------------
-- Well-founded induction on the relation _≪_
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF-ATP where

open import FOTC.Base
open import FOTC.Data.Nat

import FOTC.Data.Nat.Induction.Acc.WF-ATP
open FOTC.Data.Nat.Induction.Acc.WF-ATP.WF-<

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Induction.WF
open import FOTC.Program.McCarthy91.WF-Relation
open import FOTC.Program.McCarthy91.WF-Relation.PropertiesATP

-- Parametrized modules
open module InvImg =
  FOTC.Induction.WF.InverseImage {N} {N} {_<_} ≪-fn-N

------------------------------------------------------------------------------
-- The relation _≪_ is well-founded (using the inverse image combinator).
wf-≪ : WellFounded _≪_
wf-≪ Nn = wellFounded wf-< Nn

-- Well-founded induction on the relation _≪_.
wfInd-≪ : (A : D → Set) →
          (∀ {n} → N n → (∀ {m} → N m → m ≪ n → A m) → A n) →
          ∀ {n} → N n → A n
wfInd-≪ A = WellFoundedInduction wf-≪
