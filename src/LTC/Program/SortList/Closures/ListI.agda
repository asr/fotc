------------------------------------------------------------------------------
-- Closures properties respect to List (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Program.SortList.Closures.ListI where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.List.PropertiesI using ( ++-ListN )

open import LTC.Program.SortList.SortList
  using ( flatten ; flatten-nilTree ; flatten-node ; flatten-tip
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        )

------------------------------------------------------------------------------
-- The function flatten generates a list.
flatten-List : {t : D} → Tree t → ListN (flatten t)
flatten-List nilT =
  subst (λ t → ListN t) (sym flatten-nilTree) nilLN
flatten-List (tipT {i} Ni) =
  subst (λ t → ListN t) (sym $ flatten-tip i) (consLN Ni nilLN)

flatten-List (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂)
  = subst (λ t → ListN t)
          (sym $ flatten-node t₁ i t₂)
          (++-ListN (flatten-List Tt₁)  -- IH.
                    (flatten-List Tt₂))  -- IH.
