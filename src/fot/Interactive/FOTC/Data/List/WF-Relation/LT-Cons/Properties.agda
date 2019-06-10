------------------------------------------------------------------------------
-- Properties for the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.List.WF-Relation.LT-Cons.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length

------------------------------------------------------------------------------
-- LTC ⊆ LTL.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL Lxs (x , refl) = lg-x<lg-x∷xs x Lxs
