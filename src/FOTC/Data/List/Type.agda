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
List-ind : (P : D → Set) →
          P [] →
          (∀ x {xs} → P xs → P (x ∷ xs)) →
          ∀ {xs} → List xs → P xs
List-ind P P[] is nilL          = P[]
List-ind P P[] is (consL x Lxs) = is x (List-ind P P[] is Lxs)
