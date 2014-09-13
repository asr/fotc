------------------------------------------------------------------------------
-- Totality properties respect to Bool
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.SortList.Properties.Totality.BoolATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.Type
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

le-ItemList-Bool : ∀ {item is} → N item → ListN is → Bool (le-ItemList item is)
le-ItemList-Bool {item} Nitem lnnil = prf
  where postulate prf : Bool (le-ItemList item [])
        {-# ATP prove prf #-}

le-ItemList-Bool {item} Nitem (lncons {i} {is} Ni Lis) =
  prf (le-ItemList-Bool Nitem Lis)
  where postulate prf : Bool (le-ItemList item is) →
                        Bool (le-ItemList item (i ∷ is))
        {-# ATP prove prf &&-Bool le-Bool #-}

le-Lists-Bool : ∀ {is js} → ListN is → ListN js → Bool (le-Lists is js)
le-Lists-Bool {js = js} lnnil LNjs = prf
  where postulate prf : Bool (le-Lists [] js)
        {-# ATP prove prf #-}
le-Lists-Bool {js = js} (lncons {i} {is} Ni LNis) LNjs =
  prf (le-Lists-Bool LNis LNjs)
  where postulate prf : Bool (le-Lists is js) → Bool (le-Lists (i ∷ is) js)
        {-# ATP prove prf &&-Bool le-ItemList-Bool #-}

ordList-Bool : ∀ {is} → ListN is → Bool (ordList is)
ordList-Bool lnnil = prf
  where postulate prf : Bool (ordList [])
        {-# ATP prove prf #-}

ordList-Bool (lncons {i} {is} Ni LNis) = prf (ordList-Bool LNis)
  where postulate prf : Bool (ordList is) → Bool (ordList (i ∷ is))
        {-# ATP prove prf &&-Bool le-ItemList-Bool #-}

le-ItemTree-Bool : ∀ {item t} → N item → Tree t → Bool (le-ItemTree item t)
le-ItemTree-Bool {item} Nt tnil = prf
  where postulate prf : Bool (le-ItemTree item nil)
        {-# ATP prove prf #-}
le-ItemTree-Bool {item} Nitem (ttip {i} Ni) = prf
  where postulate prf : Bool (le-ItemTree item (tip i))
        {-# ATP prove prf le-Bool #-}
le-ItemTree-Bool {item} Nitem  (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (le-ItemTree-Bool Nitem Tt₁) (le-ItemTree-Bool Nitem Tt₂)
  where postulate prf : Bool (le-ItemTree item t₁) →
                        Bool (le-ItemTree item t₂) →
                        Bool (le-ItemTree item (node t₁ i t₂))
        {-# ATP prove prf &&-Bool #-}

le-TreeItem-Bool : ∀ {t item} → Tree t → N item → Bool (le-TreeItem t item)
le-TreeItem-Bool {item = item } tnil Nt = prf
  where postulate prf : Bool (le-TreeItem nil item)
        {-# ATP prove prf #-}
le-TreeItem-Bool {item = item} (ttip {i} Ni) Nitem = prf
  where postulate prf : Bool (le-TreeItem (tip i) item)
        {-# ATP prove prf le-Bool #-}
le-TreeItem-Bool {item = item} (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) Nitem =
  prf (le-TreeItem-Bool Tt₁ Nitem) (le-TreeItem-Bool Tt₂ Nitem)
  where postulate prf : Bool (le-TreeItem t₁ item) →
                        Bool (le-TreeItem t₂ item) →
                        Bool (le-TreeItem (node t₁ i t₂) item)
        {-# ATP prove prf &&-Bool #-}

ordTree-Bool : ∀ {t} → Tree t → Bool (ordTree t)
ordTree-Bool tnil = prf
  where postulate prf : Bool (ordTree nil)
        {-# ATP prove prf #-}

ordTree-Bool (ttip {i} Ni) = prf
  where postulate prf : Bool (ordTree (tip i))
        {-# ATP prove prf #-}

ordTree-Bool (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (ordTree-Bool Tt₁) (ordTree-Bool Tt₂)
  where postulate prf : Bool (ordTree t₁) →
                        Bool (ordTree t₂) →
                        Bool (ordTree (node t₁ i t₂))
        {-# ATP prove prf &&-Bool le-TreeItem-Bool le-ItemTree-Bool #-}
