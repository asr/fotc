------------------------------------------------------------------------------
-- A proof that is rejected using the --without-K option
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}

module Lists where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.List.WF-Relation.LT-Cons
open import FOTC.Data.List.WF-Relation.LT-Length

------------------------------------------------------------------------------
-- LTC → LTL.

-- 31 May 2013. Rejected when using the --without-K option. See
-- Agda issue 865.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL Lxs (x , refl) = lg-x<lg-x∷xs x Lxs

-- This proof is accepted using the --without-K option.
LTC→LTL' : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL' {xs} {ys} Lxs (x , h) =
  subst (λ ys' → length xs < length ys')
        (sym h)
        (lg-x<lg-x∷xs x Lxs)
