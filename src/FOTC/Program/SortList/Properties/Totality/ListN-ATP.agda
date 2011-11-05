------------------------------------------------------------------------------
-- Totality properties respect to ListN
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Totality.ListN-ATP where

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- The function flatten generates a ListN.
flatten-ListN : ∀ {t} → Tree t → ListN (flatten t)
flatten-ListN nilT = prf
  where
  postulate prf : ListN (flatten nilTree)
  {-# ATP prove prf #-}
flatten-ListN (tipT {i} Ni) = prf
  where
  postulate prf : ListN (flatten (tip i))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf #-}

flatten-ListN (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (flatten-ListN Tt₁) (flatten-ListN Tt₂)
  where
  postulate prf : ListN (flatten t₁) →  -- IH.
                  ListN (flatten t₂) →  -- IH.
                  ListN (flatten (node t₁ i t₂))
