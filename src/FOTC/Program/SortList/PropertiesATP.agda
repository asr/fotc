------------------------------------------------------------------------------
-- Properties stated in the Burstall's paper
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.PropertiesATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
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
toTree-OrdTree {item} Nitem nilT OTt = prf
  where
  postulate prf : OrdTree (toTree · item · nilTree)
  {-# ATP prove prf #-}

toTree-OrdTree {item} Nitem (tipT {i} Ni) OTt =
  [ prf₁ , prf₂ ] (x>y∨x≤y Ni Nitem)
  where
  postulate prf₁ : GT i item → OrdTree (toTree · item · tip i)
  {-# ATP prove prf₁ x≤x x<y→x≤y x>y→x≰y #-}

  postulate prf₂ : LE i item → OrdTree (toTree · item · tip i)
  {-# ATP prove prf₂ x≤x #-}

toTree-OrdTree {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTnodeT =
  [ prf₁ (toTree-OrdTree Nitem Tt₁ (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT))
         (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT)
  , prf₂ (toTree-OrdTree Nitem Tt₂ (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT))
         (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT)
  ] (x>y∨x≤y Ni Nitem)
  where
  postulate prf₁ : ordTree (toTree · item · t₁) ≡ true →  -- IH.
                   OrdTree t₂ →
                   GT i item →
                   OrdTree (toTree · item · node t₁ i t₂)
  {-# ATP prove prf₁ ≤-ItemTree-Bool ≤-TreeItem-Bool ordTree-Bool
                     x>y→x≰y &&₃-proj₃ &&₃-proj₄
                     toTree-OrdTree-helper₁
  #-}

  postulate prf₂ : ordTree (toTree · item · t₂) ≡ true → -- IH.
                   OrdTree t₁ →
                   LE i item →
                   OrdTree (toTree · item · node t₁ i t₂)
  {-# ATP prove prf₂ ≤-ItemTree-Bool ≤-TreeItem-Bool ordTree-Bool
                     &&₃-proj₃ &&₃-proj₄
                     toTree-OrdTree-helper₂
  #-}

------------------------------------------------------------------------------
-- Burstall's lemma: ord(maketree(is)).

-- makeTree-TreeOrd : ∀ {is} → ListN is → OrdTree (makeTree is)
-- makeTree-TreeOrd LNis =
--   ind-lit OrdTree toTree nilTree LNis ordTree-nilTree
--           (λ Nx y TOy → toTree-OrdTree Nx {!!} TOy)

makeTree-OrdTree : ∀ {is} → ListN is → OrdTree (makeTree is)
makeTree-OrdTree nilLN = prf
  where
  postulate prf : OrdTree (makeTree [])
  {-# ATP prove prf #-}

makeTree-OrdTree (consLN {i} {is} Ni Lis) = prf $ makeTree-OrdTree Lis
  where
  postulate prf : OrdTree (makeTree is) →  -- IH.
                  OrdTree (makeTree (i ∷ is))
  {-# ATP prove prf makeTree-Tree toTree-OrdTree #-}

------------------------------------------------------------------------------
-- Burstall's lemma: If ord(is1) and ord(is2) and is1 ≤ is2 then
-- ord(concat(is1, is2)).
++-OrdList : ∀ {is js} → ListN is → ListN js → OrdList is → OrdList js →
             LE-Lists is js → OrdList (is ++ js)

++-OrdList {js = js} nilLN LNjs LOis LOjs is≤js =
  subst (λ t → OrdList t) (sym $ ++-[] js) LOjs

++-OrdList {js = js} (consLN {i} {is} Ni LNis) LNjs OLi∷is OLjs i∷is≤js =
  subst (λ t → OrdList t)
        (sym $ ++-∷ i is js)
        (lemma (++-OrdList LNis LNjs
                           (subList-OrdList Ni LNis OLi∷is)
                           OLjs
                           (&&-proj₂ (≤-ItemList-Bool Ni LNjs)
                                     (≤-Lists-Bool LNis LNjs)
                                     (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js))))
  where
  postulate lemma : OrdList (is ++ js) →  -- IH
                    OrdList (i ∷ is ++ js)
  {-# ATP prove lemma ≤-ItemList-Bool ≤-Lists-Bool ordList-Bool
                      &&-proj₁ &&-proj₂
                      ++-OrdList-helper
  #-}

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then (flatten t) is ordered.
flatten-OrdList : ∀ {t} → Tree t → OrdTree t → OrdList (flatten t)
flatten-OrdList nilT OTt =
  subst (λ t → OrdList t) (sym flatten-nilTree) ordList-[]

flatten-OrdList (tipT {i} Ni) OTt = prf
  where
  postulate prf : OrdList (flatten (tip i))
  -- {-# ATP prove prf #-}

flatten-OrdList (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTt
  = prf (++-OrdList (flatten-ListN Tt₁)
                    (flatten-ListN Tt₂)
                    (flatten-OrdList Tt₁ (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTt)) -- IH.
                    (flatten-OrdList Tt₂ (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTt))-- IH.
                    (flatten-OrdList-helper Tt₁ Ni Tt₂ OTt))
  where
  postulate prf : OrdList (flatten t₁ ++ flatten t₂) → -- Indirect IH.
                  OrdList (flatten (node t₁ i t₂))
  {-# ATP prove prf #-}
