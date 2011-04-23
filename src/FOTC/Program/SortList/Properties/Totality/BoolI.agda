------------------------------------------------------------------------------
-- Totality properties respect to Bool
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Totality.BoolI where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Bool.Type
  using ( Bool ; tB  -- The FOTC booleans type.
        )
open import FOTC.Data.Bool.PropertiesI using ( &&-Bool ; ≤-Bool )
open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC natural numbers type.
        )

open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

≤-ItemList-Bool : ∀ {item is} → N item → ListN is → Bool (≤-ItemList item is)
≤-ItemList-Bool {item} Nitem nilLN = subst Bool (sym $ ≤-ItemList-[] item) tB
≤-ItemList-Bool {item} Nitem (consLN {i} {is} Ni Lis) =
  subst Bool
        (sym $ ≤-ItemList-∷ item i is)
        (&&-Bool (≤-Bool Nitem Ni) (≤-ItemList-Bool Nitem Lis))

-- See the ATP version.
postulate
  ≤-Lists-Bool : ∀ {is js} → ListN is → ListN js → Bool (≤-Lists is js)

-- See the ATP version.
postulate
  ordList-Bool : ∀ {is} → ListN is → Bool (ordList is)

≤-ItemTree-Bool : ∀ {item t} → N item → Tree t →
                  Bool (≤-ItemTree item t)
≤-ItemTree-Bool {item} _ nilT = subst Bool (sym $ ≤-ItemTree-nilTree item) tB
≤-ItemTree-Bool {item} Nitem (tipT {i} Ni) =
  subst Bool (sym $ ≤-ItemTree-tip item i) (≤-Bool Nitem Ni)
≤-ItemTree-Bool {item} Nitem  (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
    subst Bool
          (sym $ ≤-ItemTree-node item t₁ i t₂)
          (&&-Bool (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂))

≤-TreeItem-Bool : ∀ {t item} → Tree t → N item → Bool (≤-TreeItem t item)
≤-TreeItem-Bool {item = item} nilT _ =
  subst Bool (sym $ ≤-TreeItem-nilTree item) tB
≤-TreeItem-Bool {item = item} (tipT {i} Ni) Nitem =
  subst Bool (sym $ ≤-TreeItem-tip i item) (≤-Bool Ni Nitem)
≤-TreeItem-Bool {item = item} (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) Nitem =
  subst Bool
        (sym $ ≤-TreeItem-node t₁ i t₂ item)
        (&&-Bool (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem))

ordTree-Bool : ∀ {t} → Tree t → Bool (ordTree t)
ordTree-Bool nilT          = subst Bool (sym ordTree-nilTree) tB
ordTree-Bool (tipT {i} Ni) = subst Bool (sym $ ordTree-tip i) tB
ordTree-Bool (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  subst Bool
        (sym $ ordTree-node t₁ i t₂)
        (&&-Bool (ordTree-Bool Tt₁)
                 (&&-Bool (ordTree-Bool Tt₂)
                          (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                   (≤-ItemTree-Bool Ni Tt₂))))
