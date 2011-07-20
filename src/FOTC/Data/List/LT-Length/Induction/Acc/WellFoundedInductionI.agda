------------------------------------------------------------------------------
-- Well-founded induction on the relation LTL
------------------------------------------------------------------------------

module FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInductionI where

open import FOTC.Base

open import FOTC.Data.List
open import FOTC.Data.List.LT-Length
open import FOTC.Data.List.LT-Length.PropertiesI
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type

open import FOTC.Induction.WellFounded

-- Parametrized modules
open module InvImg =
  FOTC.Induction.WellFounded.InverseImage {List} {N} {LT} length-N

------------------------------------------------------------------------------
-- The relation LTL is well-founded (using the inverse image combinator).
wf-LTL : WellFounded LTL
wf-LTL Lxs = wellFounded wf-LT Lxs

-- Well-founded induction on the relation LTL.
wfInd-LTL : (P : D → Set) →
            (∀ {xs} → List xs → (∀ {ys} → List ys → LTL ys xs → P ys) → P xs) →
            ∀ {xs} → List xs → P xs
wfInd-LTL P = WellFoundedInduction wf-LTL

------------------------------------------------------------------------------
-- The relation LTL is well-founded (a different proof).
-- Adapted from FOTC.Data.Nat.Induction.Acc.WellFoundedInduction.WF₁-LT.
module WF₁-LTL where

wf-LTL₁ : WellFounded LTL
wf-LTL₁ Lxs = acc Lxs (helper Lxs)
  where
  helper : ∀ {xs ys} → List xs → List ys → LTL ys xs → Acc LTL ys
  helper nilL Lys ys<[] = ⊥-elim (xs<[]→⊥ Lys ys<[])
  helper (consL x {xs} Lxs) nilL []<x∷xs =
    acc nilL (λ Lys ys<[] → ⊥-elim (xs<[]→⊥ Lys ys<[]))
  helper (consL x {xs} Lxs) (consL y {ys} Lys) y∷ys<x∷xs = acc (consL y Lys)
    (λ {zs} Lzs zs<y∷ys →
       let ys<xs : LTL ys xs
           ys<xs = x∷xs<y∷ys→xs<ys Lys Lxs y∷ys<x∷xs

           zs<xs : LTL zs xs
           zs<xs = [ (λ zs<ys → <-trans Lzs Lys Lxs zs<ys ys<xs)
                   , (λ h → lg-xs≡lg-ys→ys<zx→xs<zs h ys<xs)
                   ] (xs<y∷ys→xs<ys∨lg-xs≡lg-ys Lzs Lys zs<y∷ys)

       in  helper Lxs Lzs zs<xs
    )
