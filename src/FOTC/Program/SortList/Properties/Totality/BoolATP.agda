------------------------------------------------------------------------------
-- Totality properties respect to Bool
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Totality.BoolATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

≤-ItemList-Bool : ∀ {item is} → N item → ListN is → Bool (≤-ItemList item is)
≤-ItemList-Bool {item} Nitem nilLN = prf
  where
  postulate prf : Bool (≤-ItemList item [])
  {-# ATP prove prf #-}

≤-ItemList-Bool {item} Nitem (consLN {i} {is} Ni Lis) =
  prf $ ≤-ItemList-Bool Nitem Lis
  where
  postulate prf : Bool (≤-ItemList item is) →  -- IH.
                  Bool (≤-ItemList item (i ∷ is))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf &&-Bool ≤-Bool #-}

≤-Lists-Bool : ∀ {is js} → ListN is → ListN js → Bool (≤-Lists is js)
≤-Lists-Bool {js = js} nilLN LNjs = prf
  where
  postulate prf : Bool (≤-Lists [] js)
  {-# ATP prove prf #-}
≤-Lists-Bool {js = js} (consLN {i} {is} Ni LNis) LNjs =
  prf $ ≤-Lists-Bool LNis LNjs
  where
  postulate prf : Bool (≤-Lists is js) →  -- IH.
                  Bool (≤-Lists (i ∷ is) js)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf &&-Bool ≤-ItemList-Bool #-}

ordList-Bool : ∀ {is} → ListN is → Bool (ordList is)
ordList-Bool nilLN = prf
  where
  postulate prf : Bool (ordList [])
  {-# ATP prove prf #-}

ordList-Bool (consLN {i} {is} Ni LNis) = prf $ ordList-Bool LNis
  where
  postulate prf : Bool (ordList is) →  -- IH.
                  Bool (ordList (i ∷ is))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf &&-Bool ≤-ItemList-Bool #-}

≤-ItemTree-Bool : ∀ {item t} → N item → Tree t → Bool (≤-ItemTree item t)
≤-ItemTree-Bool {item} Nt nilT = prf
  where
  postulate prf : Bool (≤-ItemTree item nilTree)
  {-# ATP prove prf #-}
≤-ItemTree-Bool {item} Nitem (tipT {i} Ni) = prf
  where
  postulate prf : Bool (≤-ItemTree item (tip i))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf ≤-Bool #-}
≤-ItemTree-Bool {item} Nitem  (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂)
  where
  postulate prf : Bool (≤-ItemTree item t₁) →  -- IH.
                  Bool (≤-ItemTree item t₂) →  -- IH.
                  Bool (≤-ItemTree item (node t₁ i t₂))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf &&-Bool #-}

≤-TreeItem-Bool : ∀ {t item} → Tree t → N item → Bool (≤-TreeItem t item)
≤-TreeItem-Bool {item = item } nilT Nt = prf
  where
  postulate prf : Bool (≤-TreeItem nilTree item)
  {-# ATP prove prf #-}
≤-TreeItem-Bool {item = item} (tipT {i} Ni) Nitem = prf
  where
  postulate prf : Bool (≤-TreeItem (tip i) item)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf ≤-Bool #-}
≤-TreeItem-Bool {item = item} (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) Nitem =
  prf (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem)
  where
  postulate prf : Bool (≤-TreeItem t₁ item) →  -- IH.
                  Bool (≤-TreeItem t₂ item) →  -- IH.
                  Bool (≤-TreeItem (node t₁ i t₂) item)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf &&-Bool #-}

ordTree-Bool : ∀ {t} → Tree t → Bool (ordTree t)
ordTree-Bool nilT = prf
  where
  postulate prf : Bool (ordTree nilTree)
  {-# ATP prove prf #-}

ordTree-Bool (tipT {i} Ni) = prf
  where
  postulate prf : Bool (ordTree (tip i))
  {-# ATP prove prf #-}

ordTree-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (ordTree-Bool Tt₁) (ordTree-Bool Tt₂)
  where
  postulate prf : Bool (ordTree t₁) →  -- IH.
                  Bool (ordTree t₂) →  -- IH.
                  Bool (ordTree (node t₁ i t₂))
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf &&-Bool ≤-TreeItem-Bool ≤-ItemTree-Bool #-}
