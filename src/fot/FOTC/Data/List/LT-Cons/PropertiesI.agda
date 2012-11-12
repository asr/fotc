------------------------------------------------------------------------------
-- Properties for the relation LTC
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.LT-Cons.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.List
open import FOTC.Data.List.LT-Length
open import FOTC.Data.List.LT-Cons
open import FOTC.Data.List.PropertiesI

------------------------------------------------------------------------------
-- LTC ⊆ LTL.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL {xs} {ys} Lxs (x , ys≡x∷xs) =
  subst (λ ys' → length xs < length ys')
        (sym ys≡x∷xs)
        (lg-x<lg-x∷xs x Lxs)
