------------------------------------------------------------------------------
-- Generic well-founded induction on list
------------------------------------------------------------------------------

-- Adapted from FOTC.Data.Nat.Induction.Acc.WellFounded.

module FOTC.Data.List.Induction.Acc.WellFounded where

open import FOTC.Base

open import FOTC.Data.Nat.Induction.Acc.WellFounded as Nat using ()
open import FOTC.Data.Nat.Type
open import FOTC.Data.List.Type

------------------------------------------------------------------------------
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
data Acc (_<_ : D → D → Set) : D → Set where
 acc : ∀ {xs} → List xs → (∀ {ys} → List ys → ys < xs → Acc _<_ ys) →
       Acc _<_ xs

accFold : {P : D → Set} (_<_ : D → D → Set) →
          (∀ {xs} → List xs → (∀ {ys} → List ys → ys < xs → P ys) → P xs) →
          ∀ {xs} → List xs → Acc _<_ xs → P xs
accFold _<_ f Lxs (acc _ h) =
  f Lxs (λ Lys ys<xs → accFold _<_ f Lys (h Lys ys<xs))

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.
WellFounded : (D → D → Set) → Set
WellFounded _<_ = ∀ {xs} → List xs → Acc _<_ xs

WellFoundedInduction :
  {P : D → Set} {_<_ : D → D → Set} →
  WellFounded _<_ →
  (∀ {xs} → List xs → (∀ {ys} → List ys → ys < xs → P ys) → P xs) →
  ∀ {xs} → List xs → P xs
WellFoundedInduction {_<_ = _<_} wf f Lxs = accFold _<_ f Lxs (wf Lxs)
