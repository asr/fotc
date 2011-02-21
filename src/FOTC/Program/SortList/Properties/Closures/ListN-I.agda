------------------------------------------------------------------------------
-- Closures properties respect to ListN
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Closures.ListN-I where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.Nat.List.PropertiesI using ( ++-ListN )

open import FOTC.Program.SortList.SortList

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
