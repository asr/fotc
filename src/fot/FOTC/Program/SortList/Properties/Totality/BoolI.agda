------------------------------------------------------------------------------
-- Totality properties respect to Bool
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.SortList.Properties.Totality.BoolI where

open import FOTC.Base
open import FOTC.Data.Bool.Type
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

le-ItemList-Bool : ∀ {item is} → N item → ListN is → Bool (le-ItemList item is)
le-ItemList-Bool {item} Nitem lnnil = subst Bool (sym (le-ItemList-[] item)) btrue
le-ItemList-Bool {item} Nitem (lncons {i} {is} Ni Lis) =
  subst Bool
        (sym (le-ItemList-∷ item i is))
        (&&-Bool (le-Bool Nitem Ni) (le-ItemList-Bool Nitem Lis))

-- See the ATP version.
postulate le-Lists-Bool : ∀ {is js} → ListN is → ListN js → Bool (le-Lists is js)

-- See the ATP version.
postulate ordList-Bool : ∀ {is} → ListN is → Bool (ordList is)

le-ItemTree-Bool : ∀ {item t} → N item → Tree t →
                  Bool (le-ItemTree item t)
le-ItemTree-Bool {item} _ tnil = subst Bool (sym (le-ItemTree-nil item)) btrue
le-ItemTree-Bool {item} Nitem (ttip {i} Ni) =
  subst Bool (sym (le-ItemTree-tip item i)) (le-Bool Nitem Ni)
le-ItemTree-Bool {item} Nitem  (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
    subst Bool
          (sym (le-ItemTree-node item t₁ i t₂))
          (&&-Bool (le-ItemTree-Bool Nitem Tt₁) (le-ItemTree-Bool Nitem Tt₂))

le-TreeItem-Bool : ∀ {t item} → Tree t → N item → Bool (le-TreeItem t item)
le-TreeItem-Bool {item = item} tnil _ =
  subst Bool (sym (le-TreeItem-nil item)) btrue
le-TreeItem-Bool {item = item} (ttip {i} Ni) Nitem =
  subst Bool (sym (le-TreeItem-tip i item)) (le-Bool Ni Nitem)
le-TreeItem-Bool {item = item} (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) Nitem =
  subst Bool
        (sym (le-TreeItem-node t₁ i t₂ item))
        (&&-Bool (le-TreeItem-Bool Tt₁ Nitem) (le-TreeItem-Bool Tt₂ Nitem))

ordTree-Bool : ∀ {t} → Tree t → Bool (ordTree t)
ordTree-Bool tnil          = subst Bool (sym ordTree-nil) btrue
ordTree-Bool (ttip {i} Ni) = subst Bool (sym (ordTree-tip i)) btrue
ordTree-Bool (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  subst Bool
        (sym (ordTree-node t₁ i t₂))
        (&&-Bool (ordTree-Bool Tt₁)
                 (&&-Bool (ordTree-Bool Tt₂)
                          (&&-Bool (le-TreeItem-Bool Tt₁ Ni)
                                   (le-ItemTree-Bool Ni Tt₂))))
