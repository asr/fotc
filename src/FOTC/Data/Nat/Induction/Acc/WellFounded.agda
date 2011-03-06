------------------------------------------------------------------------------
-- Generic well-founded induction on natural numbers
------------------------------------------------------------------------------

-- Adapted from
-- http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/
-- and the Agda standard library.

module FOTC.Data.Nat.Induction.Acc.WellFounded where

open import FOTC.Base

open import Common.Relation.Unary

open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
data Acc (_<_ : D → D → Set) : D → Set where
 acc : ∀ {n} → N n → (∀ {m} → N m → m < n → Acc _<_ m) → Acc _<_ n

accFold : {P : D → Set} (_<_ : D → D → Set) →
          (∀ {n} → N n → (∀ {m} → N m → m < n → P m) → P n) →
          ∀ {n} → N n → Acc _<_ n → P n
accFold _<_ f Nn (acc _ h) = f Nn (λ Nm m<n → accFold _<_ f Nm (h Nm m<n))

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.
WellFounded : (D → D → Set) → Set
WellFounded _<_ = ∀ {n} → N n → Acc _<_ n

WellFoundedInduction : {P : D → Set} {_<_ : D → D → Set} →
                       WellFounded _<_ →
                       (∀ {n} → N n → (∀ {m} → N m → m < n → P m) → P n) →
                       ∀ {n} → N n → P n
WellFoundedInduction {_<_ = _<_} wf f Nn = accFold _<_ f Nn (wf Nn)

module Subrelation {_<₁_ _<₂_ : D → D → Set}
                   (<₁⇒<₂ : ∀ {m n } → m <₁ n → m <₂ n) where

  accessible : Acc _<₂_ ⊆ Acc _<₁_
  accessible (acc Nn rs) =
    acc Nn (λ Nm m<n → accessible (rs Nm (<₁⇒<₂ m<n)))

  well-founded : WellFounded _<₂_ → WellFounded _<₁_
  well-founded wf = λ Nn → accessible (wf Nn)

module InverseImage {_<_ : D → D → Set}
                    {f : D → D}
                    (f-N : ∀ {n} → N n → N (f n))
                    where

  accessible : ∀ {n} → N n → Acc _<_ (f n) → Acc (λ x y → f x < f y) n
  accessible Nn (acc _ rs) =
    acc Nn (λ {m} Nm fm<fn → accessible Nm (rs (f-N Nm) fm<fn) )

  wellFounded : WellFounded _<_ → WellFounded (λ x y → f x < f y)
  wellFounded wf = λ Nn → accessible Nn (wf (f-N Nn))
