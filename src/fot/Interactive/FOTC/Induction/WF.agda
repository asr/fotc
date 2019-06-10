------------------------------------------------------------------------------
-- Well-founded induction on natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Adapted from
-- http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/
-- and the Agda standard library 0.8.1.

module Interactive.FOTC.Induction.WF where

open import Common.Relation.Unary

open import Interactive.FOTC.Base

------------------------------------------------------------------------------
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
data Acc (P : D → Set)(_<_ : D → D → Set)(x : D) : Set where
 acc : (∀ {y} → P y → y < x → Acc P _<_ y) → Acc P _<_ x

accFold : {P Q : D → Set}(_<_ : D → D → Set) →
          (∀ {x} → Q x → (∀ {y} → Q y → y < x → P y) → P x) →
          ∀ {x} → Q x → Acc Q _<_ x → P x
accFold _<_ f Qx (acc h) = f Qx (λ Qy y<x → accFold _<_ f Qy (h Qy y<x))

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.
WellFounded : {P : D → Set} → (D → D → Set) → Set
WellFounded {P} _<_ = ∀ {x} → P x → Acc P _<_ x

WellFoundedInduction : {P Q : D → Set}
                       {_<_ : D → D → Set} →
                       WellFounded _<_ →
                       (∀ {x} → Q x → (∀ {y} → Q y → y < x → P y) → P x) →
                       ∀ {x} → Q x → P x
WellFoundedInduction {_<_ = _<_} wf f Qx = accFold _<_ f Qx (wf Qx)

module Subrelation {P        : D → Set}
                   {_<_ _<'_ : D → D → Set}
                   (<⇒<'     : ∀ {x y} → P x → x < y → x <' y)
                   where

  accessible : Acc P _<'_ ⊆ Acc P _<_
  accessible (acc h) = acc (λ Py y<x → accessible (h Py (<⇒<' Py y<x)))

  well-founded : WellFounded _<'_ → WellFounded _<_
  well-founded wf = λ Px → accessible (wf Px)

module InverseImage {P Q : D → Set}
                    {_<_ : D → D → Set}
                    {f   : D → D}
                    (f-Q : ∀ {x} → P x → Q (f x))
                    where

  accessible : ∀ {x} → P x →
               Acc Q _<_ (f x) → Acc P (λ x' y' → f x' < f y') x
  accessible Px (acc h) =
    acc (λ {y} Py fy<fx → accessible Py (h (f-Q Py) fy<fx))

  wellFounded : WellFounded _<_ → WellFounded (λ x y → f x < f y)
  wellFounded wf = λ Px → accessible Px (wf (f-Q Px))
