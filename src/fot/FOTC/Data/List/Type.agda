------------------------------------------------------------------------------
-- The FOTC lists type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B. This module is re-exported by FOTC.Data.List.

module FOTC.Data.List.Type where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- The FOTC lists type (inductive predicate for total lists).
data List : D → Set where
  lnil  : List []
  lcons : ∀ x {xs} → List xs → List (x ∷ xs)
{-# ATP axioms lnil lcons #-}

-- Induction principle.
List-ind : (A : D → Set) →
           A [] →
           (∀ x {xs} → A xs → A (x ∷ xs)) →
           ∀ {xs} → List xs → A xs
List-ind A A[] h lnil          = A[]
List-ind A A[] h (lcons x Lxs) = h x (List-ind A A[] h Lxs)
