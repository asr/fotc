------------------------------------------------------------------------------
-- Well-founded induction on the relation LTC
------------------------------------------------------------------------------

open import FOTC.Base

open import FOTC.Data.List
open import FOTC.Data.List.Type
open import FOTC.Data.List.LT-Cons
open import FOTC.Data.List.LT-Length

module FOTC.Data.List.LT-Cons.Induction.Acc.WellFoundedInduction
  (xs<[]→⊥                   : ∀ {xs} → List xs → ¬ (LTL xs []))
  (x∷xs<y∷ys→xs<ys           : ∀ {x xs y ys} → List xs → List ys →
                               LTL (x ∷ xs) (y ∷ ys) → LTL xs ys)
  (<-trans                   : ∀ {xs ys zs} → List xs → List ys → List zs →
                               LTL xs ys → LTL ys zs → LTL xs zs)
  (lg-xs≡lg-ys→ys<zx→xs<zs   : ∀ {xs ys zs} → length xs ≡ length ys →
                               LTL ys zs → LTL xs zs)
  (xs<y∷ys→xs<ys∨lg-xs≡lg-ys : ∀ {xs y ys} → List xs → List ys →
                               LTL xs (y ∷ ys) →
                               LTL xs ys ∨ length xs ≡ length ys)
  (LTC→LTL                   : ∀ {xs ys} → List xs → List ys →
                               LTC xs ys → LTL xs ys)
  where

open import FOTC.Data.List.Induction.Acc.WellFounded

-- Parametrized modules

open module S = FOTC.Data.List.Induction.Acc.WellFounded.Subrelation LTC→LTL

import FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInduction
open module WF-LTC =
  FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInduction
    xs<[]→⊥
    x∷xs<y∷ys→xs<ys
    <-trans
    lg-xs≡lg-ys→ys<zx→xs<zs
    xs<y∷ys→xs<ys∨lg-xs≡lg-ys

------------------------------------------------------------------------------
-- The relation LTL is well-founded.
wf-LTC : WellFounded LTC
wf-LTC Lxs = well-founded wf-LTL Lxs

-- Well-founded induction on the relation LTC.
wfInd-LTC : (P : D → Set) →
            (∀ {xs} → List xs → (∀ {ys} → List ys → LTC ys xs → P ys) → P xs) →
            ∀ {xs} → List xs → P xs
wfInd-LTC P = WellFoundedInduction wf-LTC
