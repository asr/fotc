------------------------------------------------------------------------------
-- Well-founded induction on the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF-I where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.List.WF-Relation.LT-Cons
open import FOTC.Data.List.WF-Relation.LT-Cons.PropertiesI
open import FOTC.Data.List.WF-Relation.LT-Length
open import FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF-I
open import FOTC.Induction.WF

-- Parametrized modules
open module S = FOTC.Induction.WF.Subrelation {List} {LTC} LTC→LTL

------------------------------------------------------------------------------
-- The relation LTL is well-founded (using the subrelation combinator).
LTC-wf : WellFounded LTC
LTC-wf Lxs = well-founded LTL-wf Lxs

-- Well-founded induction on the relation LTC.
LTC-wfind : (A : D → Set) →
            (∀ {xs} → List xs → (∀ {ys} → List ys → LTC ys xs → A ys) → A xs) →
            ∀ {xs} → List xs → A xs
LTC-wfind A = WellFoundedInduction LTC-wf
