------------------------------------------------------------------------------
-- Well-founded induction on natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from
-- http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/
-- and the Agda standard library.

module FOTC.Induction.WellFounded where

open import Common.Relation.Unary

open import FOTC.Base

------------------------------------------------------------------------------
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
data Acc (T : D → Set)(_<_ : D → D → Set)(x : D) : Set where
 acc : (∀ {y} → T y → y < x → Acc T _<_ y) → Acc T _<_ x

accFold : {T P : D → Set}(_<_ : D → D → Set) →
          (∀ {x} → T x → (∀ {y} → T y → y < x → P y) → P x) →
          ∀ {x} → T x → Acc T _<_ x → P x
accFold _<_ f Tx (acc h) = f Tx (λ Ty y<x → accFold _<_ f Ty (h Ty y<x))

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.
WellFounded : {T : D → Set} → (D → D → Set) → Set
WellFounded {T} _<_ = ∀ {x} → T x → Acc T _<_ x

WellFoundedInduction : {T P : D → Set}{_<_ : D → D → Set} →
                       WellFounded _<_ →
                       (∀ {x} → T x → (∀ {y} → T y → y < x → P y) → P x) →
                       ∀ {x} → T x → P x
WellFoundedInduction {_<_ = _<_} wf f Tx = accFold _<_ f Tx (wf Tx)

module Subrelation {T : D → Set}
                   {_<₁_ _<₂_ : D → D → Set}
                   (<₁⇒<₂ : ∀ {x y} → T x → x <₁ y → x <₂ y)
                   where

  accessible : Acc T _<₂_ ⊆ Acc T _<₁_
  accessible (acc h) = acc (λ Ty y<₁x → accessible (h Ty (<₁⇒<₂ Ty y<₁x)))

  well-founded : WellFounded _<₂_ → WellFounded _<₁_
  well-founded wf = λ Tx → accessible (wf Tx)

module InverseImage {T₁ T₂ : D → Set}
                    {_<_ : D → D → Set}
                    {f : D → D}
                    (f-T₂ : ∀ {x} → T₁ x → T₂ (f x))
                    where

  accessible : ∀ {x} → T₁ x →
               Acc T₂ _<_ (f x) → Acc T₁ (λ x₁ y₁ → f x₁ < f y₁) x
  accessible T₁x (acc h) =
    acc (λ {y} T₁y fy<fx → accessible T₁y (h (f-T₂ T₁y) fy<fx))

  wellFounded : WellFounded _<_ → WellFounded (λ x y → f x < f y)
  wellFounded wf = λ Tx → accessible Tx (wf (f-T₂ Tx))
