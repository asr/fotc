------------------------------------------------------------------------------
-- Properties stated in the Burstall's paper
------------------------------------------------------------------------------

module LTC.Program.SortList.PropertiesI where

open import LTC.Base

open import Common.Function

open import LTC.Data.Bool
open import LTC.Data.Bool.PropertiesI
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesI
open import LTC.Data.Nat.List.Type
open import LTC.Data.Nat.Type
open import LTC.Data.List

open import LTC.Program.SortList.Properties.Closures.BoolI
open import LTC.Program.SortList.Properties.Closures.ListN-I
open import LTC.Program.SortList.Properties.Closures.OrdList.FlattenI
open import LTC.Program.SortList.Properties.Closures.OrdListI

open import LTC.Program.SortList.Properties.Closures.OrdTreeI
open import LTC.Program.SortList.Properties.Closures.TreeI
open import LTC.Program.SortList.SortList

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- Induction on lit.
ind-lit : (P : D → Set)(f y₀ : D) → {xs : D} → ListN xs →
          P y₀ →
          ({x : D} → N x → (y : D) → P y → P (f · x · y)) →
          P (lit f xs y₀)
ind-lit P f y₀ nilLN Py₀ iStep = subst (λ t → P t) (sym (lit-[] f y₀)) Py₀
ind-lit P f y₀ (consLN {i} {is} Ni LNis) Py₀ iStep =
  subst (λ t → P t)
        (sym (lit-∷ f i is y₀))
        (iStep Ni (lit f is y₀) (ind-lit P f y₀ LNis Py₀ iStep))

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then totree(i, t) is ordered.
toTree-OrdTree : {item t : D} → N item → Tree t → OrdTree t →
                 OrdTree (toTree · item · t)
toTree-OrdTree {item} Nitem nilT _ =
  begin
    ordTree (toTree · item · nilTree)
      ≡⟨ subst (λ x → ordTree (toTree · item · nilTree) ≡
                     ordTree x)
               (toTree-nilTree item)
               refl
      ⟩
    ordTree (tip item)
      ≡⟨ ordTree-tip item ⟩
    true
  ∎

toTree-OrdTree {item} Nitem (tipT {i} Ni) _ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Ni Nitem)
  where
    prf₁ : GT i item → OrdTree (toTree · item · tip i)
    prf₁ i>item =
      begin
        ordTree (toTree · item · tip i)
          ≡⟨ subst (λ t → ordTree (toTree · item · tip i) ≡ ordTree t)
                   (toTree-tip item i)
                   refl
          ⟩
        ordTree (if (i ≤ item)
                    then (node (tip i) item (tip item))
                    else (node (tip item) i (tip i)))
           ≡⟨ subst (λ t → ordTree (if (i ≤ item)
                                       then (node (tip i) item (tip item))
                                       else (node (tip item) i (tip i))) ≡
                           ordTree (if t
                                       then (node (tip i) item (tip item))
                                       else (node (tip item) i (tip i))))
                    (x>y→x≰y Ni Nitem i>item)
                    refl
           ⟩
        ordTree (if false
                    then (node (tip i) item (tip item))
                    else (node (tip item) i (tip i)))
          ≡⟨ subst (λ t → ordTree (if false
                                      then (node (tip i) item (tip item))
                                      else (node (tip item) i (tip i))) ≡
                                      ordTree t)
                   (if-false (node (tip item) i (tip i)))
                   refl
          ⟩
        ordTree (node (tip item) i (tip i))
          ≡⟨ ordTree-node (tip item) i (tip i) ⟩
        ordTree (tip item)      &&
        ordTree (tip i)         &&
        ≤-TreeItem (tip item) i &&
        ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → ordTree (tip item)      &&
                          ordTree (tip i)         &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i)    ≡
                          t                       &&
                          ordTree (tip i)         &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i))
                   (ordTree-tip item)
                   refl
          ⟩
        true && ordTree (tip i) && ≤-TreeItem (tip item) i &&
        ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → true                    &&
                          ordTree (tip i)         &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i)    ≡
                          true                    &&
                          t                       &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i))
                   (ordTree-tip i)
                   refl
          ⟩
        true && true && ≤-TreeItem (tip item) i && ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → true && true && ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i) ≡
                          true && true && t && ≤-ItemTree i (tip i))
                   (≤-TreeItem-tip item i)
                   refl
          ⟩
        true && true && item ≤ i && ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → true && true && item ≤ i && ≤-ItemTree i (tip i) ≡
                          true && true && t && ≤-ItemTree i (tip i))
                   (x<y→x≤y Nitem Ni i>item)
                   refl
          ⟩
        true && true && true && ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → true && true && true && ≤-ItemTree i (tip i) ≡
                          true && true && true && t)
                   (≤-ItemTree-tip i i)
                   refl
          ⟩
        true && true && true && i ≤ i
          ≡⟨ subst (λ t → true && true && true && i ≤ i ≡
                          true && true && true && t)
                   (x≤x Ni)
                   refl
          ⟩
        true && true && true && true
          ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
                   &&-tt
                   refl
          ⟩
        true && true && true
          ≡⟨ subst (λ t → true && true && true ≡ true && t)
                   &&-tt
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

    prf₂ : LE i item → OrdTree (toTree · item · tip i)
    prf₂ i≤item =
      begin
        ordTree (toTree · item · tip i)
          ≡⟨ subst (λ t → ordTree (toTree · item · tip i) ≡ ordTree t)
                   (toTree-tip item i)
                   refl
          ⟩
        ordTree (if (i ≤ item)
                    then (node (tip i) item (tip item))
                    else (node (tip item) i (tip i)))
           ≡⟨ subst (λ t → ordTree (if (i ≤ item)
                                       then (node (tip i) item (tip item))
                                       else (node (tip item) i (tip i))) ≡
                           ordTree (if t
                                       then (node (tip i) item (tip item))
                                       else (node (tip item) i (tip i))))
                    (i≤item)
                    refl
           ⟩
        ordTree (if true
                    then (node (tip i) item (tip item))
                    else (node (tip item) i (tip i)))
          ≡⟨ subst (λ t → ordTree (if true
                                      then (node (tip i) item (tip item))
                                      else (node (tip item) i (tip i))) ≡
                          ordTree t)
                   (if-true (node (tip i) item (tip item)))
                   refl
          ⟩
        ordTree (node (tip i) item (tip item))
          ≡⟨ ordTree-node (tip i) item (tip item) ⟩
        ordTree (tip i) && ordTree (tip item) && ≤-TreeItem (tip i) item &&
        ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → ordTree (tip i)             &&
                          ordTree (tip item)          &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item)  ≡
                          t                           &&
                          ordTree (tip item)          &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item))
                   (ordTree-tip i)
                   refl
          ⟩
        true && ordTree (tip item) && ≤-TreeItem (tip i) item &&
        ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → true                        &&
                          ordTree (tip item)          &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item)  ≡
                          true                        &&
                          t                           &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item))
                   (ordTree-tip item)
                   refl
          ⟩
        true && true && ≤-TreeItem (tip i) item && ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → true && true && ≤-TreeItem (tip i) item &&
                          ≤-ItemTree item (tip item) ≡
                          true && true && t && ≤-ItemTree item (tip item))
                   (≤-TreeItem-tip i item)
                   refl
          ⟩
        true && true && i ≤ item && ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → true && true && i ≤ item && ≤-ItemTree item (tip item) ≡
                          true && true && t && ≤-ItemTree item (tip item))
                   i≤item
                   refl
          ⟩
        true && true && true && ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → true && true && true && ≤-ItemTree item (tip item) ≡
                          true && true && true && t)
                   (≤-ItemTree-tip item item)
                   refl
          ⟩
        true && true && true && item ≤ item
          ≡⟨ subst (λ t → true && true && true && item ≤ item ≡
                          true && true && true && t)
                   (x≤x Nitem)
                   refl
          ⟩
        true && true && true && true
          ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
                   &&-tt
                   refl
          ⟩
        true && true && true
          ≡⟨ subst (λ t → true && true && true ≡ true && t) &&-tt refl ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

toTree-OrdTree {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTnodeT =
  [ prf₁ , prf₂ ] (x>y∨x≤y Ni Nitem)
  where
    prf₁ : GT i item → OrdTree (toTree · item · node t₁ i t₂)
    prf₁ i>item =
      begin
        ordTree (toTree · item · node t₁ i t₂)
          ≡⟨ subst (λ t → ordTree (toTree · item · node t₁ i t₂) ≡ ordTree t)
                   (toTree-node item t₁ i t₂)
                   refl
          ⟩
        ordTree (if (i ≤ item)
                    then (node t₁ i (toTree · item · t₂))
                    else (node (toTree · item · t₁) i t₂))
           ≡⟨ subst (λ t → ordTree (if (i ≤ item)
                                       then (node t₁ i (toTree · item · t₂))
                                       else (node (toTree · item · t₁) i t₂)) ≡
                           ordTree (if t
                                       then (node t₁ i (toTree · item · t₂))
                                       else (node (toTree · item · t₁) i t₂)))
                    (x>y→x≰y Ni Nitem i>item)
                    refl
           ⟩
        ordTree (if false
                    then (node t₁ i (toTree · item · t₂))
                    else (node (toTree · item · t₁) i t₂))
          ≡⟨ subst (λ t → ordTree (if false
                                      then (node t₁ i (toTree · item · t₂))
                                      else (node (toTree · item · t₁) i t₂)) ≡
                          ordTree t)
                   (if-false (node (toTree · item · t₁) i t₂))
                   refl
          ⟩
        ordTree (node (toTree · item · t₁) i t₂)
          ≡⟨ ordTree-node (toTree · item · t₁) i t₂ ⟩
        ordTree (toTree · item · t₁)      &&
        ordTree t₂                        &&
        ≤-TreeItem (toTree · item · t₁) i &&
        ≤-ItemTree i t₂
          ≡⟨ subst (λ t → ordTree (toTree · item · t₁)      &&
                          ordTree t₂                        &&
                          ≤-TreeItem (toTree · item · t₁) i &&
                          ≤-ItemTree i t₂                   ≡
                          t                                 &&
                          ordTree t₂                        &&
                          ≤-TreeItem (toTree · item · t₁) i &&
                          ≤-ItemTree i t₂)
                   -- IH.
                   (toTree-OrdTree Nitem Tt₁
                                   (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT))
                   refl
          ⟩
        true && ordTree t₂ && ≤-TreeItem (toTree · item · t₁) i &&
        ≤-ItemTree i t₂
          ≡⟨ subst (λ t → true                              &&
                          ordTree t₂                        &&
                          ≤-TreeItem (toTree · item · t₁) i &&
                          ≤-ItemTree i t₂                   ≡
                          true                              &&
                          t                                 &&
                          ≤-TreeItem (toTree · item · t₁) i &&
                          ≤-ItemTree i t₂)
                   (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT)
                   refl
          ⟩
        true && true && ≤-TreeItem (toTree · item · t₁) i && ≤-ItemTree i t₂
          ≡⟨ subst (λ t → true                              &&
                          true                              &&
                          ≤-TreeItem (toTree · item · t₁) i &&
                          ≤-ItemTree i t₂                   ≡
                          true && true && t && ≤-ItemTree i t₂)
                   (toTree-OrdTree-aux₁ Ni Nitem i>item Tt₁
                     ((&&₃-proj₃
                        (ordTree-Bool Tt₁)
                        (ordTree-Bool Tt₂)
                        (≤-TreeItem-Bool Tt₁ Ni)
                        (≤-ItemTree-Bool Ni Tt₂)
                        (trans (sym $ ordTree-node t₁ i t₂) OTnodeT))))
                   refl
          ⟩
        true && true && true && ≤-ItemTree i t₂
          ≡⟨ subst (λ t → true && true && true && ≤-ItemTree i t₂ ≡
                       true && true && true && t)
                   (&&₃-proj₄
                     (ordTree-Bool Tt₁)
                     (ordTree-Bool Tt₂)
                     (≤-TreeItem-Bool Tt₁ Ni)
                     (≤-ItemTree-Bool Ni Tt₂)
                     (trans (sym $ ordTree-node t₁ i t₂) OTnodeT))
                   refl
          ⟩
        true && true && true && true
          ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
                   &&-tt
                   refl
          ⟩
        true && true && true
          ≡⟨ subst (λ t → true && true && true ≡ true && t) &&-tt refl ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

    prf₂ : LE i item → OrdTree (toTree · item · node t₁ i t₂)
    prf₂ i≤item =
      begin
        ordTree (toTree · item · node t₁ i t₂)
          ≡⟨ subst (λ t → ordTree (toTree · item · node t₁ i t₂) ≡ ordTree t)
                   (toTree-node item t₁ i t₂)
                   refl
          ⟩
        ordTree (if (i ≤ item)
                    then (node t₁ i (toTree · item · t₂))
                    else (node (toTree · item · t₁) i t₂))
           ≡⟨ subst (λ t → ordTree (if (i ≤ item)
                                       then (node t₁ i (toTree · item · t₂))
                                       else (node (toTree · item · t₁) i t₂)) ≡
                           ordTree (if t
                                       then (node t₁ i (toTree · item · t₂))
                                       else (node (toTree · item · t₁) i t₂)))
                    i≤item
                    refl
           ⟩
        ordTree (if true
                    then (node t₁ i (toTree · item · t₂))
                    else (node (toTree · item · t₁) i t₂))
          ≡⟨ subst (λ t → ordTree (if true
                                      then (node t₁ i (toTree · item · t₂))
                                      else (node (toTree · item · t₁) i t₂)) ≡
                          ordTree t)
                   (if-true (node t₁ i (toTree · item · t₂)))
                   refl
          ⟩
        ordTree (node t₁ i (toTree · item · t₂))
          ≡⟨ ordTree-node t₁ i (toTree · item · t₂) ⟩
        ordTree t₁                     &&
        ordTree (toTree · item · t₂)   &&
        ≤-TreeItem t₁ i                &&
        ≤-ItemTree i (toTree · item · t₂)
          ≡⟨ subst (λ t → ordTree t₁                        &&
                          ordTree (toTree · item · t₂)      &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree · item · t₂) ≡
                          t                                 &&
                          ordTree (toTree · item · t₂)      &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree · item · t₂))
                   (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT)
                   refl
          ⟩
        true && ordTree (toTree · item · t₂) && ≤-TreeItem t₁ i &&
        ≤-ItemTree i (toTree · item · t₂)
          ≡⟨ subst (λ t → true                              &&
                          ordTree (toTree · item · t₂)      &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree · item · t₂) ≡
                          true                              &&
                          t                                 &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree · item · t₂))
                   -- IH.
                   (toTree-OrdTree Nitem Tt₂
                     (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTnodeT))
                   refl
          ⟩
        true && true && ≤-TreeItem t₁ i && ≤-ItemTree i (toTree · item · t₂)
          ≡⟨ subst (λ t → true                              &&
                          true                              &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree · item · t₂) ≡
                          true                              &&
                          true                              &&
                          t                                 &&
                          ≤-ItemTree i (toTree · item · t₂))
                   (&&₃-proj₃
                     (ordTree-Bool Tt₁)
                     (ordTree-Bool Tt₂)
                     (≤-TreeItem-Bool Tt₁ Ni)
                     (≤-ItemTree-Bool Ni Tt₂)
                     (trans (sym $ ordTree-node t₁ i t₂) OTnodeT))
                   refl
          ⟩
        true && true && true && ≤-ItemTree i (toTree · item · t₂)
          ≡⟨ subst (λ t → true                              &&
                          true                              &&
                          true                              &&
                          ≤-ItemTree i (toTree · item · t₂) ≡
                          true && true && true && t)
                    (toTree-OrdTree-aux₂ Ni Nitem i≤item Tt₂
                      ((&&₃-proj₄
                        (ordTree-Bool Tt₁)
                        (ordTree-Bool Tt₂)
                        (≤-TreeItem-Bool Tt₁ Ni)
                        (≤-ItemTree-Bool Ni Tt₂)
                        (trans (sym $ ordTree-node t₁ i t₂) OTnodeT))))
                    refl
          ⟩
        true && true && true && true
          ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
                   &&-tt
                   refl
          ⟩
        true && true && true
          ≡⟨ subst (λ t → true && true && true ≡ true && t) &&-tt refl ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

------------------------------------------------------------------------------
-- Burstall's lemma: ord(maketree(is)).

-- makeTree-TreeOrd : {is : D} → ListN is → OrdTree (makeTree is)
-- makeTree-TreeOrd LNis =
--   ind-lit OrdTree toTree nilTree LNis ordTree-nilTree
--           (λ Nx y TOy → toTree-OrdTree Nx {!!} TOy)

makeTree-OrdTree : {is : D} → ListN is → OrdTree (makeTree is)
makeTree-OrdTree nilLN =
  begin
      ordTree (lit toTree [] nilTree)
        ≡⟨ subst (λ t → ordTree (lit toTree [] nilTree) ≡ ordTree t)
                 (lit-[] toTree nilTree)
                 refl
        ⟩
      ordTree nilTree ≡⟨ ordTree-nilTree ⟩
      true
      ∎

makeTree-OrdTree (consLN {i} {is} Ni Lis) =
  begin
    ordTree (lit toTree (i ∷ is) nilTree)
      ≡⟨ subst (λ t → ordTree (lit toTree (i ∷ is) nilTree) ≡ ordTree t)
               (lit-∷ toTree i is nilTree)
               refl
      ⟩
    ordTree (toTree · i · (lit toTree is nilTree))
      ≡⟨ toTree-OrdTree Ni (makeTree-Tree Lis) (makeTree-OrdTree Lis) ⟩
    true
  ∎

------------------------------------------------------------------------------
-- Burstall's lemma: If ord(is1) and ord(is2) and is1 ≤ is2 then
-- ord(concat(is1, is2)).
++-OrdList : {is js : D} → ListN is → ListN js → OrdList is → OrdList js →
             LE-Lists is js → OrdList (is ++ js)

++-OrdList {js = js} nilLN LNjs LOis LOjs is≤js =
  subst (λ t → OrdList t) (sym $ ++-[] js) LOjs

++-OrdList {js = js} (consLN {i} {is} Ni LNis) LNjs LOi∷is LOjs i∷is≤js =
  subst (λ t → OrdList t) (sym $ ++-∷ i is js) lemma
  where
    lemma : OrdList (i ∷ is ++ js)
    lemma =
      begin
        ordList (i ∷ is ++ js)
          ≡⟨ ordList-∷ i (is ++ js) ⟩
        ≤-ItemList i (is ++ js) && ordList (is ++ js)
          ≡⟨ subst (λ t → ≤-ItemList i (is ++ js) && ordList (is ++ js) ≡
                          t && ordList (is ++ js))
                   (++-OrdList-aux Ni LNis LNjs
                     (&&-proj₁ (≤-ItemList-Bool Ni LNis)
                               (ordList-Bool LNis)
                               (trans (sym (ordList-∷ i is)) LOi∷is))
                     (&&-proj₁ (≤-ItemList-Bool Ni LNjs)
                               (≤-Lists-Bool LNis LNjs)
                               (trans (sym (≤-Lists-∷ i is js)) i∷is≤js))
                     (&&-proj₂ (≤-ItemList-Bool Ni LNjs)
                               (≤-Lists-Bool LNis LNjs)
                               (trans (sym (≤-Lists-∷ i is js)) i∷is≤js))
                   )
                   refl
          ⟩
        true && ordList (is ++ js)
          ≡⟨ subst (λ t → true && ordList (is ++ js) ≡ true && t)
                   -- IH.
                   (++-OrdList LNis LNjs (subList-OrdList Ni LNis LOi∷is) LOjs
                               (&&-proj₂
                                 (≤-ItemList-Bool Ni LNjs)
                                 (≤-Lists-Bool LNis LNjs)
                                 (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)))
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then (flatten t) is ordered.
flatten-OrdList : {t : D} → Tree t → OrdTree t → OrdList (flatten t)
flatten-OrdList nilT OTt =
  subst (λ t → OrdList t) (sym flatten-nilTree) ordList-[]

flatten-OrdList (tipT {i} Ni) OTt =
  begin
    ordList (flatten (tip i))
      ≡⟨ subst (λ t → ordList (flatten (tip i)) ≡ ordList t)
               (flatten-tip i)
               refl
      ⟩
    ordList (i ∷ [])
      ≡⟨ ordList-∷ i [] ⟩
    ≤-ItemList i [] && ordList []
      ≡⟨ subst₂ (λ t₁ t₂ → ≤-ItemList i [] && ordList [] ≡ t₁ && t₂)
                (≤-ItemList-[] i)
                ordList-[]
                refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true
  ∎

flatten-OrdList (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTt =
  begin
    ordList (flatten (node t₁ i t₂))
      ≡⟨ subst (λ t → ordList (flatten (node t₁ i t₂)) ≡ ordList t)
               (flatten-node t₁ i t₂)
               refl
      ⟩
    ordList (flatten t₁ ++ flatten t₂)
      ≡⟨ ++-OrdList (flatten-ListN Tt₁)
                    (flatten-ListN Tt₂)
                    -- IH.
                    (flatten-OrdList Tt₁ (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTt))
                    -- IH.
                    (flatten-OrdList Tt₂ (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTt))
                    (flatten-OrdList-aux Tt₁ Ni Tt₂ OTt)
      ⟩
    true
  ∎
