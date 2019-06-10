------------------------------------------------------------------------------
-- Totality properties respect to ListN
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.SortList.Properties.Totality.ListN where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.List.Type
open import Combined.FOTC.Data.Nat.List.Properties
open import Combined.FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- The function flatten generates a ListN.
flatten-ListN : ∀ {t} → Tree t → ListN (flatten t)
flatten-ListN tnil = prf
  where postulate prf : ListN (flatten nil)
        {-# ATP prove prf #-}
flatten-ListN (ttip {i} Ni) = prf
  where postulate prf : ListN (flatten (tip i))
        {-# ATP prove prf #-}

flatten-ListN (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (flatten-ListN Tt₁) (flatten-ListN Tt₂)
  where postulate prf : ListN (flatten t₁) →
                        ListN (flatten t₂) →
                        ListN (flatten (node t₁ i t₂))
