------------------------------------------------------------------------------
-- Well-founded induction on natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Adapted from
-- http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/
-- and the Agda standard library 0.8.1.

module FOT.FOTC.Data.Nat.Induction.Acc.WF-I where

open import FOTC.Base

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
data AccLT : D → Set where
 accLT : ∀ {x} → N x → (∀ {y} → N y → y < x → AccLT y) → AccLT x

accFoldLT : {P : D → Set} →
            (∀ {x} → N x → (∀ {y} → N y → y < x → P y) → P x) →
            ∀ {x} → N x → AccLT x → P x
accFoldLT f Nx (accLT _ h) = f Nx (λ Ny y<x → accFoldLT f Ny (h Ny y<x))

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then LT is
-- well-founded.
WellFoundedLT : Set
WellFoundedLT = ∀ {x} → N x → AccLT x

WellFoundedInductionLT : {P : D → Set} →
                         WellFoundedLT →
                         (∀ {x} → N x → (∀ {y} → N y → y < x → P y) → P x) →
                         ∀ {x} → N x → P x
WellFoundedInductionLT wf f Nx = accFoldLT f Nx (wf Nx)
