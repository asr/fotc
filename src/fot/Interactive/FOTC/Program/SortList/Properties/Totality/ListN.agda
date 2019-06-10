------------------------------------------------------------------------------
-- Totality properties respect to ListN
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.SortList.Properties.Totality.ListN where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.List.Type
open import Interactive.FOTC.Data.Nat.List.Properties
open import Interactive.FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- The function flatten generates a ListN.
flatten-ListN : ∀ {t} → Tree t → ListN (flatten t)
flatten-ListN tnil = subst ListN (sym flatten-nil) lnnil
flatten-ListN (ttip {i} Ni) =
  subst ListN (sym (flatten-tip i)) (lncons Ni lnnil)
flatten-ListN (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂)
  = subst ListN
          (sym (flatten-node t₁ i t₂))
          (++-ListN (flatten-ListN Tt₁)
                    (flatten-ListN Tt₂))
