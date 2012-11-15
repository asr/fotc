------------------------------------------------------------------------------
-- Well-founded induction on natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from
-- http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/
-- and the Agda standard library.

module FOTC.Induction.WF where

open import Common.Relation.Unary

open import FOTC.Base

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

WellFoundedInduction : {P Q : D → Set}{_<_ : D → D → Set} →
                       WellFounded _<_ →
                       (∀ {x} → Q x → (∀ {y} → Q y → y < x → P y) → P x) →
                       ∀ {x} → Q x → P x
WellFoundedInduction {_<_ = _<_} wf f Qx = accFold _<_ f Qx (wf Qx)

module Subrelation {P : D → Set}
                   {_<₁_ _<₂_ : D → D → Set}
                   (<₁⇒<₂ : ∀ {x y} → P x → x <₁ y → x <₂ y)
                   where

  accessible : Acc P _<₂_ ⊆ Acc P _<₁_
  accessible (acc h) = acc (λ Py y<₁x → accessible (h Py (<₁⇒<₂ Py y<₁x)))

  well-founded : WellFounded _<₂_ → WellFounded _<₁_
  well-founded wf = λ Px → accessible (wf Px)

module InverseImage {P₁ P₂ : D → Set}
                    {_<_ : D → D → Set}
                    {f : D → D}
                    (f-P₂ : ∀ {x} → P₁ x → P₂ (f x))
                    where

  accessible : ∀ {x} → P₁ x →
               Acc P₂ _<_ (f x) → Acc P₁ (λ x₁ y₁ → f x₁ < f y₁) x
  accessible P₁x (acc h) =
    acc (λ {y} P₁y fy<fx → accessible P₁y (h (f-P₂ P₁y) fy<fx))

  wellFounded : WellFounded _<_ → WellFounded (λ x y → f x < f y)
  wellFounded wf = λ Px → accessible Px (wf (f-P₂ Px))
