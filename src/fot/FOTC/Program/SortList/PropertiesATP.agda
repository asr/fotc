------------------------------------------------------------------------------
-- Properties stated in the Burstall's paper
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.SortList.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesATP
open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.Properties.Totality.ListN-ATP
open import FOTC.Program.SortList.Properties.Totality.OrdList.FlattenATP
open import FOTC.Program.SortList.Properties.Totality.OrdListATP
open import FOTC.Program.SortList.Properties.Totality.OrdTreeATP
open import FOTC.Program.SortList.Properties.Totality.TreeATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then totree(i, t) is ordered.
toTree-OrdTree : ∀ {item t} → N item → Tree t → OrdTree t →
                 OrdTree (toTree · item · t)
toTree-OrdTree {item} Nitem tnil OTt = prf
  where postulate prf : OrdTree (toTree · item · nil)
        {-# ATP prove prf #-}

toTree-OrdTree {item} Nitem (ttip {i} Ni) OTt =
  case prf₁ prf₂ (x>y∨x≤y Ni Nitem)
  where
  postulate prf₁ : i > item → OrdTree (toTree · item · tip i)
  {-# ATP prove prf₁ x≤x x<y→x≤y x>y→x≰y #-}

  postulate prf₂ : i ≤ item → OrdTree (toTree · item · tip i)
  {-# ATP prove prf₂ x≤x #-}

toTree-OrdTree {item} Nitem (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTtnode =
  case (prf₁ (toTree-OrdTree Nitem Tt₁ (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode))
             (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode))
       (prf₂ (toTree-OrdTree Nitem Tt₂ (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode))
             (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode))
       (x>y∨x≤y Ni Nitem)
  where
  postulate prf₁ : ordTree (toTree · item · t₁) ≡ true →
                   OrdTree t₂ →
                   i > item →
                   OrdTree (toTree · item · node t₁ i t₂)
  {-# ATP prove prf₁ &&-list₄-t x>y→x≰y le-ItemTree-Bool le-TreeItem-Bool ordTree-Bool toTree-OrdTree-helper₁ #-}

  postulate prf₂ : ordTree (toTree · item · t₂) ≡ true →
                   OrdTree t₁ →
                   i ≤ item →
                   OrdTree (toTree · item · node t₁ i t₂)
  {-# ATP prove prf₂ &&-list₄-t  le-ItemTree-Bool le-TreeItem-Bool ordTree-Bool toTree-OrdTree-helper₂ #-}

------------------------------------------------------------------------------
-- Burstall's lemma: ord(maketree(is)).

-- makeTree-TreeOrd : ∀ {is} → ListN is → OrdTree (makeTree is)
-- makeTree-TreeOrd LNis =
--   ind-lit OrdTree toTree nil LNis ordTree-nil
--           (λ Nx y TOy → toTree-OrdTree Nx {!!} TOy)

makeTree-OrdTree : ∀ {is} → ListN is → OrdTree (makeTree is)
makeTree-OrdTree lnnil = prf
  where postulate prf : OrdTree (makeTree [])
        {-# ATP prove prf #-}

makeTree-OrdTree (lncons {i} {is} Ni Lis) = prf (makeTree-OrdTree Lis)
  where postulate prf : OrdTree (makeTree is) → OrdTree (makeTree (i ∷ is))
        {-# ATP prove prf makeTree-Tree toTree-OrdTree #-}

------------------------------------------------------------------------------
-- Burstall's lemma: If ord(is1) and ord(is2) and is1 ≤ is2 then
-- ord(concat(is1, is2)).
++-OrdList : ∀ {is js} → ListN is → ListN js → OrdList is → OrdList js →
             ≤-Lists is js → OrdList (is ++ js)

++-OrdList {js = js} lnnil LNjs LOis LOjs is≤js =
  subst OrdList (sym (++-leftIdentity js)) LOjs

++-OrdList {js = js} (lncons {i} {is} Ni LNis) LNjs OLi∷is OLjs i∷is≤js =
  subst OrdList
        (sym (++-∷ i is js))
        (lemma (++-OrdList LNis LNjs
                           (subList-OrdList Ni LNis OLi∷is)
                           OLjs
                           (&&-list₂-t₂ (le-ItemList-Bool Ni LNjs)
                                        (le-Lists-Bool LNis LNjs)
                                        (trans (sym (le-Lists-∷ i is js)) i∷is≤js))))
  where postulate lemma : OrdList (is ++ js) → OrdList (i ∷ is ++ js)
        {-# ATP prove lemma &&-list₂-t ++-OrdList-helper le-ItemList-Bool le-Lists-Bool ordList-Bool #-}

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then (flatten t) is ordered.
flatten-OrdList : ∀ {t} → Tree t → OrdTree t → OrdList (flatten t)
flatten-OrdList tnil OTt =
  subst OrdList (sym flatten-nil) ordList-[]

flatten-OrdList (ttip {i} Ni) OTt = prf
  where postulate prf : OrdList (flatten (tip i))
        {-# ATP prove prf #-}

flatten-OrdList (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTt
  = prf (++-OrdList (flatten-ListN Tt₁)
                    (flatten-ListN Tt₂)
                    (flatten-OrdList Tt₁ (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTt))
                    (flatten-OrdList Tt₂ (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTt))
                    (flatten-OrdList-helper Tt₁ Ni Tt₂ OTt))
  where postulate prf : OrdList (flatten t₁ ++ flatten t₂) → -- Indirect IH.
                        OrdList (flatten (node t₁ i t₂))
        {-# ATP prove prf #-}
