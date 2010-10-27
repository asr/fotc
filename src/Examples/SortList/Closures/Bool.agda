------------------------------------------------------------------------------
-- Closures properties respect to Bool
------------------------------------------------------------------------------

module Examples.SortList.Closures.Bool where

open import LTC.Minimal

open import Examples.SortList.SortList
  using ( ≤-ItemList
        ; ≤-ItemTree
        ; ≤-Lists
        ; ≤-TreeItem
        ; isListOrd
        ; isTreeOrd
        ; nilTree ; node ; tip
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        )

open import LTC.Data.Bool using ( Bool )
open import LTC.Data.Bool.Properties using ( &&-Bool ; ≤-Bool )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type using ( N )

------------------------------------------------------------------------------
≤-ItemList-Bool : {item : D} → N item → {is : D} → ListN is →
                  Bool (≤-ItemList item is)
≤-ItemList-Bool {item} Nitem nilLN = prf
  where
    postulate prf : Bool (≤-ItemList item [])
    {-# ATP prove prf #-}

≤-ItemList-Bool {item} Nitem (consLN {i} {is} Ni Lis) =
  prf (≤-ItemList-Bool Nitem Lis)
  where
    postulate prf : Bool (≤-ItemList item is) →  -- IH.
                    Bool (≤-ItemList item (i ∷ is))
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf &&-Bool ≤-Bool #-}

≤-Lists-Bool : {is js : D} → ListN is → ListN js → Bool (≤-Lists is js)
≤-Lists-Bool {js = js} nilLN LNjs = prf
  where
    postulate prf : Bool (≤-Lists [] js)
    {-# ATP prove prf #-}
≤-Lists-Bool {js = js} (consLN {i} {is} Ni LNis) LNjs =
  prf (≤-Lists-Bool LNis LNjs)
  where
    postulate prf : Bool (≤-Lists is js) →  -- IH.
                    Bool (≤-Lists (i ∷ is) js)
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf &&-Bool ≤-ItemList-Bool #-}

isListOrd-Bool : {is : D} → ListN is → Bool (isListOrd is)
isListOrd-Bool nilLN = prf
  where
    postulate prf : Bool (isListOrd [])
    {-# ATP prove prf #-}

isListOrd-Bool (consLN {i} {is} Ni LNis) = prf (isListOrd-Bool LNis)
  where
    postulate prf : Bool (isListOrd is) →  -- IH.
                    Bool (isListOrd (i ∷ is))
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf &&-Bool ≤-ItemList-Bool #-}

≤-ItemTree-Bool : {item : D} → N item → {t : D} → Tree t →
                  Bool (≤-ItemTree item t)
≤-ItemTree-Bool {item} _ nilT = prf
  where
    postulate prf : Bool (≤-ItemTree item nilTree)
    {-# ATP prove prf #-}
≤-ItemTree-Bool {item} Nitem (tipT {i} Ni) = prf
  where
    postulate prf : Bool (≤-ItemTree item (tip i))
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf ≤-Bool #-}
≤-ItemTree-Bool {item} Nitem  (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂)
  where
    postulate prf : Bool (≤-ItemTree item t₁) →  -- IH.
                    Bool (≤-ItemTree item t₂) →  -- IH.
                    Bool (≤-ItemTree item (node t₁ i t₂))
    -- E 1.2 no-success due to timeout (180 sec).
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf &&-Bool #-}

≤-TreeItem-Bool : {t : D} → Tree t → {item : D} → N item →
                  Bool (≤-TreeItem t item)
≤-TreeItem-Bool nilT {item} _ = prf
  where
    postulate prf : Bool (≤-TreeItem nilTree item)
    {-# ATP prove prf #-}
≤-TreeItem-Bool (tipT {i} Ni) {item} Nitem = prf
  where
    postulate prf : Bool (≤-TreeItem (tip i) item)
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf ≤-Bool #-}
≤-TreeItem-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) {item} Nitem =
  prf (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem)
  where
    postulate prf : Bool (≤-TreeItem t₁ item) →  -- IH.
                    Bool (≤-TreeItem t₂ item) →  -- IH.
                    Bool (≤-TreeItem (node t₁ i t₂) item)
    -- E 1.2 no-success due to timeout (180 sec).
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf &&-Bool #-}

isTreeOrd-Bool : {t : D} → Tree t → Bool (isTreeOrd t)
isTreeOrd-Bool nilT = prf
  where
    postulate prf : Bool (isTreeOrd nilTree)
    {-# ATP prove prf #-}

isTreeOrd-Bool (tipT {i} Ni) = prf
  where
    postulate prf : Bool (isTreeOrd (tip i))
    {-# ATP prove prf #-}

isTreeOrd-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (isTreeOrd-Bool Tt₁) (isTreeOrd-Bool Tt₂)
  where
    postulate prf : Bool (isTreeOrd t₁) →  -- IH.
                    Bool (isTreeOrd t₂) →  -- IH.
                    Bool (isTreeOrd (node t₁ i t₂))
    -- E 1.2 no-success due to timeout (180 sec).
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf &&-Bool ≤-TreeItem-Bool ≤-ItemTree-Bool #-}
