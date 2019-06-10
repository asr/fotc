------------------------------------------------------------------------------
-- Properties for the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.List.WF-Relation.LT-Cons.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.List.Properties
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons
open import Combined.FOTC.Data.List.WF-Relation.LT-Length

------------------------------------------------------------------------------
-- LTC ⊆ LTL.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL Lxs (x , refl) = lg-x<lg-x∷xs x Lxs
