------------------------------------------------------------------------------
-- The FOTC lists type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B. This module is re-exported by Interactive.FOTC.Data.List.

module Interactive.FOTC.Data.List.Type where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List

------------------------------------------------------------------------------
-- The FOTC lists type (inductive predicate for total lists).
data List : D → Set where
  lnil  : List []
  lcons : ∀ x {xs} → List xs → List (x ∷ xs)

-- Induction principle.
List-ind : (A : D → Set) →
           A [] →
           (∀ x {xs} → A xs → A (x ∷ xs)) →
           ∀ {xs} → List xs → A xs
List-ind A A[] h lnil          = A[]
List-ind A A[] h (lcons x Lxs) = h x (List-ind A A[] h Lxs)
