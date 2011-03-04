------------------------------------------------------------------------------
-- The FOTC list type
------------------------------------------------------------------------------

module FOTC.Data.List.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC list type.
data List : D → Set where
  nilL  : List []
  consL : ∀ x {xs} → (Lxs : List xs) → List (x ∷ xs)

-- Induction principle for List.
indList : (P : D → Set) →
          P [] →
          (∀ x {xs} → List xs → P xs → P (x ∷ xs)) →
          ∀ {xs} → List xs → P xs
indList P P[] iStep nilL          = P[]
indList P P[] iStep (consL x Lxs) = iStep x Lxs (indList P P[] iStep Lxs)
