------------------------------------------------------------------------------
-- Well-founded induction on the relation _◁_
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module Interactive.FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat

import Interactive.FOTC.Data.Nat.Induction.Acc.WF
open Interactive.FOTC.Data.Nat.Induction.Acc.WF.<-WF using ( <-wf )

open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Induction.WF
open import Interactive.FOTC.Program.McCarthy91.WF-Relation
open import Interactive.FOTC.Program.McCarthy91.WF-Relation.Properties

-- Parametrized modules
open module InvImg =
  Interactive.FOTC.Induction.WF.InverseImage {N} {N} {_<_} ◁-fn-N

------------------------------------------------------------------------------
-- The relation _◁_ is well-founded (using the inverse image combinator).
◁-wf : WellFounded _◁_
◁-wf Nn = wellFounded <-wf Nn

-- Well-founded induction on the relation _◁_.
◁-wfind : (A : D → Set) →
          (∀ {n} → N n → (∀ {m} → N m → m ◁ n → A m) → A n) →
          ∀ {n} → N n → A n
◁-wfind A = WellFoundedInduction ◁-wf
