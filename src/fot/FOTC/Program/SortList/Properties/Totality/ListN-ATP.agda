------------------------------------------------------------------------------
-- Totality properties respect to ListN
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.ListN-ATP where

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- The function flatten generates a ListN.
flatten-ListN : ∀ {t} → Tree t → ListN (flatten t)
flatten-ListN nilT = prf
  where postulate prf : ListN (flatten nilTree)
        {-# ATP prove prf #-}
flatten-ListN (tipT {i} Ni) = prf
  where postulate prf : ListN (flatten (tip i))
        {-# ATP prove prf #-}

flatten-ListN (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (flatten-ListN Tt₁) (flatten-ListN Tt₂)
  where postulate prf : ListN (flatten t₁) →
                        ListN (flatten t₂) →
                        ListN (flatten (node t₁ i t₂))
