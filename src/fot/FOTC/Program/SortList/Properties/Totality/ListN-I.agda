------------------------------------------------------------------------------
-- Totality properties respect to ListN
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.ListN-I where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.List.PropertiesI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- The function flatten generates a ListN.
flatten-ListN : ∀ {t} → Tree t → ListN (flatten t)
flatten-ListN tnil =
  subst (λ t → ListN t) (sym flatten-nilTree) lnnil
flatten-ListN (ttip {i} Ni) =
  subst (λ t → ListN t) (sym $ flatten-tip i) (lncons Ni lnnil)

flatten-ListN (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂)
  = subst (λ t → ListN t)
          (sym $ flatten-node t₁ i t₂)
          (++-ListN (flatten-ListN Tt₁)
                    (flatten-ListN Tt₂))
