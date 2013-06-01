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
-- 01 June 2013. This proof could use pattern matching on _≡_. See
-- Agda issue 865.
--
-- LTC ⊆ LTL.
LTC→LTL : ∀ {xs ys} → List xs → LTC xs ys → LTL xs ys
LTC→LTL {xs} {ys} Lxs (x , ys≡x∷xs) =
  subst (λ ys' → length xs < length ys')
        (sym ys≡x∷xs)
        (lg-x<lg-x∷xs x Lxs)
