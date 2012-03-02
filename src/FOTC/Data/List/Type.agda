------------------------------------------------------------------------------
-- The FOTC list type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module is re-exported by FOTC.Data.List.

module FOTC.Data.List.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC list type.
data List : D → Set where
  nilL  :                              List []
  consL : ∀ x {xs} → (Lxs : List xs) → List (x ∷ xs)
{-# ATP axiom nilL consL #-}

-- Induction principle for List.
List-ind : (A : D → Set) →
          A [] →
          (∀ x {xs} → A xs → A (x ∷ xs)) →
          ∀ {xs} → List xs → A xs
List-ind A A[] is nilL          = A[]
List-ind A A[] is (consL x Lxs) = is x (List-ind A A[] is Lxs)
