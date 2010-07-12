------------------------------------------------------------------------------
-- Closures properties respect to List
------------------------------------------------------------------------------

module Examples.SortList.Closures.List where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.SortList

open import LTC.Data.Nat.List

open import Postulates using ( []-N ; ++-List )

------------------------------------------------------------------------------

-- The function flatten generates a list.
flatten-List : {t : D} → Tree t → List (flatten t)
flatten-List nilT = prf
  where
    postulate prf : List (flatten nilTree)
    {-# ATP prove prf #-}
flatten-List (tipT {i} Ni) = prf
  where
    postulate prf : List (flatten (tip i))
    {-# ATP prove prf []-N #-}

flatten-List (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (flatten-List Tt₁) (flatten-List Tt₂)
  where
    postulate prf : List (flatten t₁) → -- IH.
                    List (flatten t₂) → -- IH.
                    List (flatten (node t₁ i t₂))
