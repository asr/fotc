------------------------------------------------------------------------------
-- Properties for the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.WF-Relation.LT-Cons.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.List.WF-Relation.LT-Cons
open import FOTC.Data.List.WF-Relation.LT-Length

------------------------------------------------------------------------------
-- LTC ⊆ LTL.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL Lxs (x , refl) = lg-x<lg-x∷xs x Lxs
