------------------------------------------------------------------------------
-- Closures properties respect to Bool (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.BoolER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.SortList

open import LTC.Data.Bool
open import LTC.Data.Bool.PropertiesER using ( &&-Bool ; ≤-Bool )
open import LTC.Data.Nat.List
open import LTC.Data.Nat.Type

------------------------------------------------------------------------------

≤-ItemList-Bool : {item : D} → N item → {is : D} → List is →
                  Bool ( ≤-ItemList item is)
≤-ItemList-Bool {item} Nitem nilL =
  subst (λ t → Bool t) (sym (≤-ItemList-[] item)) tB
≤-ItemList-Bool {item} Nitem (consL {i} {is} Ni Nis Lis) =
  subst (λ t → Bool t)
        (sym (≤-ItemList-∷ item i is))
        (&&-Bool (≤-Bool Nitem Ni) (≤-ItemList-Bool Nitem Lis))

-- See the ATP version.
postulate
  ≤-Lists-Bool : {is js : D} → List is → List js → Bool (≤-Lists is js)

-- See the ATP version.
postulate
  isListOrd-Bool : {is : D} → List is → Bool (isListOrd is)

≤-ItemTree-Bool : {item : D} → N item → {t : D} → Tree t →
                  Bool ( ≤-ItemTree item t)
≤-ItemTree-Bool {item} _ nilT =
  subst (λ t → Bool t) (sym (≤-ItemTree-nilTree item)) tB
≤-ItemTree-Bool {item} Nitem  (tipT {i} Ni) =
  subst (λ t → Bool t) (sym (≤-ItemTree-tip item i )) (≤-Bool Nitem Ni)
≤-ItemTree-Bool {item} Nitem  (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
    subst (λ t → Bool t)
        (sym (≤-ItemTree-node item t₁ i t₂))
        (&&-Bool (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂))

≤-TreeItem-Bool : {t : D} → Tree t → {item : D} → N item →
                  Bool ( ≤-TreeItem t item)
≤-TreeItem-Bool nilT {item} _ =
  subst (λ t → Bool t) (sym (≤-TreeItem-nilTree item)) tB
≤-TreeItem-Bool (tipT {i} Ni) {item} Nitem =
  subst (λ t → Bool t) (sym (≤-TreeItem-tip i item)) (≤-Bool Ni Nitem)
≤-TreeItem-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) {item} Nitem =
  subst (λ t → Bool t)
        (sym (≤-TreeItem-node t₁ i t₂ item))
        (&&-Bool (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem))

isTreeOrd-Bool : {t : D} → Tree t → Bool (isTreeOrd t)
isTreeOrd-Bool nilT = subst (λ t → Bool t) (sym isTreeOrd-nilTree) tB
isTreeOrd-Bool (tipT {i} Ni ) = subst (λ t → Bool t) (sym (isTreeOrd-tip i)) tB
isTreeOrd-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂ ) =
  subst (λ t → Bool t)
        (sym (isTreeOrd-node t₁ i t₂))
        (&&-Bool (isTreeOrd-Bool Tt₁)
                 (&&-Bool (isTreeOrd-Bool Tt₂)
                          (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                   (≤-ItemTree-Bool Ni Tt₂))))
