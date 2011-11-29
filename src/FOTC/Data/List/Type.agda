------------------------------------------------------------------------------
-- The FOTC list type
------------------------------------------------------------------------------

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
indList : (P : D → Set) →
          P [] →
          (∀ x {xs} → P xs → P (x ∷ xs)) →
          ∀ {xs} → List xs → P xs
indList P P[] is nilL          = P[]
indList P P[] is (consL x Lxs) = is x (indList P P[] is Lxs)
