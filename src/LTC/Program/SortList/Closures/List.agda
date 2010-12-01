------------------------------------------------------------------------------
-- Closures properties respect to List
------------------------------------------------------------------------------

module LTC.Program.SortList.Closures.List where

open import LTC.Base

open import LTC.Data.Nat.List.Type
  using ( ListN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.List.Properties using ( ++-ListN )

open import LTC.Program.SortList.SortList
  using ( flatten
        ; nilTree ; node ; tip
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        )

------------------------------------------------------------------------------
-- The function flatten generates a list.
flatten-List : {t : D} → Tree t → ListN (flatten t)
flatten-List nilT = prf
  where
    postulate prf : ListN (flatten nilTree)
    {-# ATP prove prf #-}
flatten-List (tipT {i} Ni) = prf
  where
    postulate prf : ListN (flatten (tip i))
    {-# ATP prove prf #-}

flatten-List (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (flatten-List Tt₁) (flatten-List Tt₂)
  where
    postulate prf : ListN (flatten t₁) →  -- IH.
                    ListN (flatten t₂) →  -- IH.
                    ListN (flatten (node t₁ i t₂))
