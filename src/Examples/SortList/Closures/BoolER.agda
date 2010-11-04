------------------------------------------------------------------------------
-- Closures properties respect to Bool (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.BoolER where

open import LTC.Base
open import LTC.BaseER using ( subst )

open import Examples.SortList.SortList
  using ( ≤-ItemList ; ≤-ItemList-[] ; ≤-ItemList-∷
        ; ≤-ItemTree ; ≤-ItemTree-nilTree ; ≤-ItemTree-node ; ≤-ItemTree-tip
        ; ≤-Lists
        ; ≤-TreeItem ; ≤-TreeItem-nilTree ; ≤-TreeItem-node ; ≤-TreeItem-tip
        ; isListOrd
        ; isTreeOrd ; isTreeOrd-nilTree ; isTreeOrd-node ; isTreeOrd-tip
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        )

open import LTC.Data.Bool
  using ( Bool ; tB  -- The LTC booleans type.
        )
open import LTC.Data.Bool.PropertiesER using ( &&-Bool ; ≤-Bool )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type using ( N )

------------------------------------------------------------------------------

≤-ItemList-Bool : {item : D} → N item → {is : D} → ListN is →
                  Bool (≤-ItemList item is)
≤-ItemList-Bool {item} Nitem nilLN = subst Bool (sym (≤-ItemList-[] item)) tB
≤-ItemList-Bool {item} Nitem (consLN {i} {is} Ni Lis) =
  subst Bool
        (sym (≤-ItemList-∷ item i is))
        (&&-Bool (≤-Bool Nitem Ni) (≤-ItemList-Bool Nitem Lis))

-- See the ATP version.
postulate
  ≤-Lists-Bool : {is js : D} → ListN is → ListN js → Bool (≤-Lists is js)

-- See the ATP version.
postulate
  isListOrd-Bool : {is : D} → ListN is → Bool (isListOrd is)

≤-ItemTree-Bool : {item : D} → N item → {t : D} → Tree t →
                  Bool (≤-ItemTree item t)
≤-ItemTree-Bool {item} _ nilT = subst Bool (sym (≤-ItemTree-nilTree item)) tB
≤-ItemTree-Bool {item} Nitem  (tipT {i} Ni) =
  subst Bool (sym (≤-ItemTree-tip item i)) (≤-Bool Nitem Ni)
≤-ItemTree-Bool {item} Nitem  (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
    subst Bool
          (sym (≤-ItemTree-node item t₁ i t₂))
          (&&-Bool (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂))

≤-TreeItem-Bool : {t : D} → Tree t → {item : D} → N item →
                  Bool (≤-TreeItem t item)
≤-TreeItem-Bool nilT {item} _ = subst Bool (sym (≤-TreeItem-nilTree item)) tB
≤-TreeItem-Bool (tipT {i} Ni) {item} Nitem =
  subst Bool (sym (≤-TreeItem-tip i item)) (≤-Bool Ni Nitem)
≤-TreeItem-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) {item} Nitem =
  subst Bool
        (sym (≤-TreeItem-node t₁ i t₂ item))
        (&&-Bool (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem))

isTreeOrd-Bool : {t : D} → Tree t → Bool (isTreeOrd t)
isTreeOrd-Bool nilT          = subst Bool (sym isTreeOrd-nilTree) tB
isTreeOrd-Bool (tipT {i} Ni) = subst Bool (sym (isTreeOrd-tip i)) tB
isTreeOrd-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  subst Bool
        (sym (isTreeOrd-node t₁ i t₂))
        (&&-Bool (isTreeOrd-Bool Tt₁)
                 (&&-Bool (isTreeOrd-Bool Tt₂)
                          (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                   (≤-ItemTree-Bool Ni Tt₂))))
