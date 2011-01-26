------------------------------------------------------------------------------
-- Closures properties respect to ListN
------------------------------------------------------------------------------

module LTC.Program.SortList.Properties.Closures.ListN-I where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.List.PropertiesI using ( ++-ListN )

open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- The function flatten generates a ListN.
flatten-ListN : ∀ {t} → Tree t → ListN (flatten t)
flatten-ListN nilT =
  subst (λ t → ListN t) (sym flatten-nilTree) nilLN
flatten-ListN (tipT {i} Ni) =
  subst (λ t → ListN t) (sym $ flatten-tip i) (consLN Ni nilLN)

flatten-ListN (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂)
  = subst (λ t → ListN t)
          (sym $ flatten-node t₁ i t₂)
          (++-ListN (flatten-ListN Tt₁)  -- IH.
                    (flatten-ListN Tt₂))  -- IH.
