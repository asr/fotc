------------------------------------------------------------------------------
-- Well-founded induction on the relation LTL
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF-I where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.List.WF-Relation.LT-Length
open import FOTC.Data.List.WF-Relation.LT-Length.PropertiesI

import FOTC.Data.Nat.Induction.Acc.WF-I
open FOTC.Data.Nat.Induction.Acc.WF-I.<-WF

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type
open import FOTC.Induction.WF

-- Parametrized modules
open module InvImg =
  FOTC.Induction.WF.InverseImage {List} {N} {_<_} lengthList-N

------------------------------------------------------------------------------
-- The relation LTL is well-founded (using the inverse image combinator).
LTL-wf : WellFounded LTL
LTL-wf Lxs = wellFounded <-wf Lxs

-- Well-founded induction on the relation LTL.
LTL-wfind : (A : D → Set) →
            (∀ {xs} → List xs → (∀ {ys} → List ys → LTL ys xs → A ys) → A xs) →
            ∀ {xs} → List xs → A xs
LTL-wfind A = WellFoundedInduction LTL-wf

------------------------------------------------------------------------------
-- The relation LTL is well-founded (a different proof).
-- Adapted from FOTC.Data.Nat.Induction.Acc.WellFoundedInduction.WF₁-LT.
module WF₁-LTL where

LTL-wf' : WellFounded LTL
LTL-wf' Lxs = acc (helper Lxs)
  where
  helper : ∀ {xs ys} → List xs → List ys → LTL ys xs → Acc List LTL ys
  helper lnil Lys ys<[] = ⊥-elim (xs<[]→⊥ Lys ys<[])
  helper (lcons x {xs} Lxs) lnil []<x∷xs =
    acc (λ Lys ys<[] → ⊥-elim (xs<[]→⊥ Lys ys<[]))
  helper (lcons x {xs} Lxs) (lcons y {ys} Lys) y∷ys<x∷xs =
    acc (λ {zs} Lzs zs<y∷ys →
           let ys<xs : LTL ys xs
               ys<xs = x∷xs<y∷ys→xs<ys Lys Lxs y∷ys<x∷xs

               zs<xs : LTL zs xs
               zs<xs = case (λ zs<ys → <-trans Lzs Lys Lxs zs<ys ys<xs)
                            (λ h → lg-xs≡lg-ys→ys<zx→xs<zs h ys<xs)
                            (xs<y∷ys→xs<ys∨lg-xs≡lg-ys Lzs Lys zs<y∷ys)

           in  helper Lxs Lzs zs<xs
        )
