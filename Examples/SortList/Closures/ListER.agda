------------------------------------------------------------------------------
-- Closures properties respect to List (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.ListER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.SortList

open import LTC.Data.Nat.List.Type
open import LTC.Data.Nat.List.PropertiesER using ( ++-ListN )

------------------------------------------------------------------------------
-- The function flatten generates a list.
flatten-List : {t : D} → Tree t → ListN (flatten t)
flatten-List nilT =
  subst (λ t → ListN t) (sym flatten-nilTree) nilLN
flatten-List (tipT {i} Ni) =
  subst (λ t → ListN t) (sym (flatten-tip i)) (consLN Ni nilLN)

flatten-List (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂)
  = subst (λ t → ListN t)
          (sym (flatten-node t₁ i t₂))
          (++-ListN (flatten-List Tt₁)  -- IH.
                    (flatten-List Tt₂)) -- IH.
