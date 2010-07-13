------------------------------------------------------------------------------
-- The LTC list type
------------------------------------------------------------------------------

module LTC.Data.List.Type where

open import LTC.Minimal

open import LTC.Data.List

------------------------------------------------------------------------------

-- The LTC list type
data List : D → Set where
  nilL  : List []
  consL : (d : D){ds : D} → (Lds : List ds) → List (d ∷ ds)

-- Induction principle for List
indList : (P : D → Set) →
          P [] →
          ((d : D){ds : D} → List ds → P ds → P (d ∷ ds)) →
          {ds : D} → List ds → P ds
indList P p[] iStep nilL               = p[]
indList P p[] iStep (consL d {ds} Lds) = iStep d Lds (indList P p[] iStep Lds)
