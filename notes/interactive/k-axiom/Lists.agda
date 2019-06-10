------------------------------------------------------------------------------
-- A proof that is rejected using the --without-K option
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Lists where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length

------------------------------------------------------------------------------
-- LTC → LTL.

-- 25 April 2014. The proof is accepted using Cockx's --without-K
-- implementation.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL Lxs (x , refl) = lg-x<lg-x∷xs x Lxs

LTC→LTL' : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL' {xs} {ys} Lxs (x , h) =
  subst (λ ys' → length xs < length ys')
        (sym h)
        (lg-x<lg-x∷xs x Lxs)
