------------------------------------------------------------------------------
-- Closures properties respect to List (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.ListER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.SortList

open import LTC.Data.Nat.List

open import Postulates using ( ++-List )

------------------------------------------------------------------------------

-- The function flatten generates a list.
flatten-List : {t : D} → Tree t → List (flatten t)
flatten-List nilT =
  subst (λ t → List t) (sym flatten-nilTree) nilL
flatten-List (tipT {i} Ni) =
  subst (λ t → List t) (sym (flatten-tip i)) (consL Ni nilL)

flatten-List (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂)
  = subst (λ t → List t)
          (sym (flatten-node t₁ i t₂))
          (++-List (flatten-List Tt₁)  -- IH.
                   (flatten-List Tt₂)) -- IH.

