------------------------------------------------------------------------------
-- Totality properties respect to Bool
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.BoolI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool.Type
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

≤-ItemList-Bool : ∀ {item is} → N item → ListN is → Bool (≤-ItemList item is)
≤-ItemList-Bool {item} Nitem lnnil = subst Bool (sym $ ≤-ItemList-[] item) btrue
≤-ItemList-Bool {item} Nitem (lncons {i} {is} Ni Lis) =
  subst Bool
        (sym $ ≤-ItemList-∷ item i is)
        (&&-Bool (≤-Bool Nitem Ni) (≤-ItemList-Bool Nitem Lis))

-- See the ATP version.
postulate ≤-Lists-Bool : ∀ {is js} → ListN is → ListN js → Bool (≤-Lists is js)

-- See the ATP version.
postulate ordList-Bool : ∀ {is} → ListN is → Bool (ordList is)

≤-ItemTree-Bool : ∀ {item t} → N item → Tree t →
                  Bool (≤-ItemTree item t)
≤-ItemTree-Bool {item} _ tnil = subst Bool (sym $ ≤-ItemTree-nil item) btrue
≤-ItemTree-Bool {item} Nitem (ttip {i} Ni) =
  subst Bool (sym $ ≤-ItemTree-tip item i) (≤-Bool Nitem Ni)
≤-ItemTree-Bool {item} Nitem  (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
    subst Bool
          (sym $ ≤-ItemTree-node item t₁ i t₂)
          (&&-Bool (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂))

≤-TreeItem-Bool : ∀ {t item} → Tree t → N item → Bool (≤-TreeItem t item)
≤-TreeItem-Bool {item = item} tnil _ =
  subst Bool (sym $ ≤-TreeItem-nil item) btrue
≤-TreeItem-Bool {item = item} (ttip {i} Ni) Nitem =
  subst Bool (sym $ ≤-TreeItem-tip i item) (≤-Bool Ni Nitem)
≤-TreeItem-Bool {item = item} (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) Nitem =
  subst Bool
        (sym $ ≤-TreeItem-node t₁ i t₂ item)
        (&&-Bool (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem))

ordTree-Bool : ∀ {t} → Tree t → Bool (ordTree t)
ordTree-Bool tnil          = subst Bool (sym ordTree-nil) btrue
ordTree-Bool (ttip {i} Ni) = subst Bool (sym $ ordTree-tip i) btrue
ordTree-Bool (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  subst Bool
        (sym $ ordTree-node t₁ i t₂)
        (&&-Bool (ordTree-Bool Tt₁)
                 (&&-Bool (ordTree-Bool Tt₂)
                          (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                   (≤-ItemTree-Bool Ni Tt₂))))
