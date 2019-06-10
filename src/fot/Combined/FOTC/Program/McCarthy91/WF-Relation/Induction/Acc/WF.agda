------------------------------------------------------------------------------
-- Well-founded induction on the relation _◁_
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module Combined.FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat

import Combined.FOTC.Data.Nat.Induction.Acc.WF
open Combined.FOTC.Data.Nat.Induction.Acc.WF.<-WF using ( <-wf )

open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.UnaryNumbers
open import Combined.FOTC.Induction.WF
open import Combined.FOTC.Program.McCarthy91.WF-Relation
open import Combined.FOTC.Program.McCarthy91.WF-Relation.Properties

-- Parametrized modules
open module InvImg =
  Combined.FOTC.Induction.WF.InverseImage {N} {N} {_<_} ◁-fn-N

------------------------------------------------------------------------------
-- The relation _◁_ is well-founded (using the inverse image combinator).
◁-wf : WellFounded _◁_
◁-wf Nn = wellFounded <-wf Nn

-- Well-founded induction on the relation _◁_.
◁-wfind : (A : D → Set) →
          (∀ {n} → N n → (∀ {m} → N m → m ◁ n → A m) → A n) →
          ∀ {n} → N n → A n
◁-wfind A = WellFoundedInduction ◁-wf
