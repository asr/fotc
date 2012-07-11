------------------------------------------------------------------------------
-- The FOTC lists type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.List.

module FOTC.Data.List.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC lists type (inductive predicate for total lists).
data List : D → Set where
  nilL  :                              List []
  consL : ∀ x {xs} → (Lxs : List xs) → List (x ∷ xs)
{-# ATP axiom nilL consL #-}

-- Induction principle.
List-ind : (A : D → Set) →
          A [] →
          (∀ x {xs} → A xs → A (x ∷ xs)) →
          ∀ {xs} → List xs → A xs
List-ind A A[] is nilL          = A[]
List-ind A A[] is (consL x Lxs) = is x (List-ind A A[] is Lxs)
