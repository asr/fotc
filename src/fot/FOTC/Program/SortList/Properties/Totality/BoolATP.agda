------------------------------------------------------------------------------
-- Totality properties respect to Bool
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

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
≤-ItemList-Bool {item} Nitem lnnil = prf
  where postulate prf : Bool (≤-ItemList item [])
        {-# ATP prove prf #-}

≤-ItemList-Bool {item} Nitem (lncons {i} {is} Ni Lis) =
  prf $ ≤-ItemList-Bool Nitem Lis
  where postulate prf : Bool (≤-ItemList item is) →
                        Bool (≤-ItemList item (i ∷ is))
        {-# ATP prove prf &&-Bool ≤-Bool #-}

≤-Lists-Bool : ∀ {is js} → ListN is → ListN js → Bool (≤-Lists is js)
≤-Lists-Bool {js = js} lnnil LNjs = prf
  where postulate prf : Bool (≤-Lists [] js)
        {-# ATP prove prf #-}
≤-Lists-Bool {js = js} (lncons {i} {is} Ni LNis) LNjs =
  prf $ ≤-Lists-Bool LNis LNjs
  where postulate prf : Bool (≤-Lists is js) → Bool (≤-Lists (i ∷ is) js)
        {-# ATP prove prf &&-Bool ≤-ItemList-Bool #-}

ordList-Bool : ∀ {is} → ListN is → Bool (ordList is)
ordList-Bool lnnil = prf
  where postulate prf : Bool (ordList [])
        {-# ATP prove prf #-}

ordList-Bool (lncons {i} {is} Ni LNis) = prf $ ordList-Bool LNis
  where postulate prf : Bool (ordList is) → Bool (ordList (i ∷ is))
        {-# ATP prove prf &&-Bool ≤-ItemList-Bool #-}

≤-ItemTree-Bool : ∀ {item t} → N item → Tree t → Bool (≤-ItemTree item t)
≤-ItemTree-Bool {item} Nt tnil = prf
  where postulate prf : Bool (≤-ItemTree item nilTree)
        {-# ATP prove prf #-}
≤-ItemTree-Bool {item} Nitem (ttip {i} Ni) = prf
  where postulate prf : Bool (≤-ItemTree item (tip i))
        {-# ATP prove prf ≤-Bool #-}
≤-ItemTree-Bool {item} Nitem  (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (≤-ItemTree-Bool Nitem Tt₁) (≤-ItemTree-Bool Nitem Tt₂)
  where postulate prf : Bool (≤-ItemTree item t₁) →
                        Bool (≤-ItemTree item t₂) →
                        Bool (≤-ItemTree item (node t₁ i t₂))
        {-# ATP prove prf &&-Bool #-}

≤-TreeItem-Bool : ∀ {t item} → Tree t → N item → Bool (≤-TreeItem t item)
≤-TreeItem-Bool {item = item } tnil Nt = prf
  where postulate prf : Bool (≤-TreeItem nilTree item)
        {-# ATP prove prf #-}
≤-TreeItem-Bool {item = item} (ttip {i} Ni) Nitem = prf
  where postulate prf : Bool (≤-TreeItem (tip i) item)
        {-# ATP prove prf ≤-Bool #-}
≤-TreeItem-Bool {item = item} (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) Nitem =
  prf (≤-TreeItem-Bool Tt₁ Nitem) (≤-TreeItem-Bool Tt₂ Nitem)
  where postulate prf : Bool (≤-TreeItem t₁ item) →
                        Bool (≤-TreeItem t₂ item) →
                        Bool (≤-TreeItem (node t₁ i t₂) item)
        {-# ATP prove prf &&-Bool #-}

ordTree-Bool : ∀ {t} → Tree t → Bool (ordTree t)
ordTree-Bool tnil = prf
  where postulate prf : Bool (ordTree nilTree)
        {-# ATP prove prf #-}

ordTree-Bool (ttip {i} Ni) = prf
  where postulate prf : Bool (ordTree (tip i))
        {-# ATP prove prf #-}

ordTree-Bool (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (ordTree-Bool Tt₁) (ordTree-Bool Tt₂)
  where postulate prf : Bool (ordTree t₁) →
                        Bool (ordTree t₂) →
                        Bool (ordTree (node t₁ i t₂))
        {-# ATP prove prf &&-Bool ≤-TreeItem-Bool ≤-ItemTree-Bool #-}
