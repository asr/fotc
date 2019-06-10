------------------------------------------------------------------------------
-- Well-founded induction on the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons.Properties
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF
open import Interactive.FOTC.Induction.WF

-- Parametrized modules
open module S = Interactive.FOTC.Induction.WF.Subrelation {List} {LTC} LTC→LTL

------------------------------------------------------------------------------
-- The relation LTL is well-founded (using the subrelation combinator).
LTC-wf : WellFounded LTC
LTC-wf Lxs = well-founded LTL-wf Lxs

-- Well-founded induction on the relation LTC.
LTC-wfind : (A : D → Set) →
            (∀ {xs} → List xs → (∀ {ys} → List ys → LTC ys xs → A ys) → A xs) →
            ∀ {xs} → List xs → A xs
LTC-wfind A = WellFoundedInduction LTC-wf
