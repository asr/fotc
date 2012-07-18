------------------------------------------------------------------------------
-- Generic well-founded induction on trees
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from FOTC.Data.Nat.Induction.Acc.WellFounded.

module Examples.FOTC.Program.Mirror.Induction.Acc.WellFounded where

open import FOTC.Base

open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
data Acc (_<_ : D → D → Set)(t : D) : Set where
 acc : (∀ {t'} → Tree t' → t' < t → Acc _<_ t') → Acc _<_ t

accFold : {P : D → Set}(_<_ : D → D → Set) →
          (∀ {t} → Tree t → (∀ {t'} → Tree t' → t' < t → P t') → P t) →
          ∀ {t} → Tree t → Acc _<_ t → P t
accFold _<_ f Tt (acc h) = f Tt (λ Tt' t'<t → accFold _<_ f Tt' (h Tt' t'<t))

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.
WellFounded : (D → D → Set) → Set
WellFounded _<_ = ∀ {t} → Tree t → Acc _<_ t

WellFoundedInduction :
  {P : D → Set}{_<_ : D → D → Set} →
  WellFounded _<_ →
  (∀ {t} → Tree t → (∀ {t'} → Tree t' → t' < t → P t') → P t) →
  ∀ {t} → Tree t → P t
WellFoundedInduction {_<_ = _<_} wf f Tt = accFold _<_ f Tt (wf Tt)
