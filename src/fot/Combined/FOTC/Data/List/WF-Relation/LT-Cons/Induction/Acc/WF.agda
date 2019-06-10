------------------------------------------------------------------------------
-- Well-founded induction on the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons.Properties
open import Combined.FOTC.Data.List.WF-Relation.LT-Length
open import Combined.FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF
open import Combined.FOTC.Induction.WF

-- Parametrized modules
open module S = Combined.FOTC.Induction.WF.Subrelation {List} {LTC} LTC→LTL

------------------------------------------------------------------------------
-- The relation LTL is well-founded (using the subrelation combinator).
LTC-wf : WellFounded LTC
LTC-wf Lxs = well-founded LTL-wf Lxs

-- Well-founded induction on the relation LTC.
LTC-wfind : (A : D → Set) →
            (∀ {xs} → List xs → (∀ {ys} → List ys → LTC ys xs → A ys) → A xs) →
            ∀ {xs} → List xs → A xs
LTC-wfind A = WellFoundedInduction LTC-wf
