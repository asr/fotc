------------------------------------------------------------------------------
-- Properties stated in the Burstall's paper
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function


open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.Properties.Totality.ListN-I
open import FOTC.Program.SortList.Properties.Totality.OrdList.FlattenI
open import FOTC.Program.SortList.Properties.Totality.OrdListI
open import FOTC.Program.SortList.Properties.Totality.OrdTreeI
open import FOTC.Program.SortList.Properties.Totality.TreeI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- Induction on lit.
ind-lit : (A : D → Set) (f : D) → ∀ y₀ {xs} → ListN xs →
          A y₀ →
          (∀ {x} → N x → ∀ y → A y → A (f · x · y)) →
          A (lit f xs y₀)
ind-lit A f y₀ lnnil Ay₀ ih = subst (λ t → A t) (sym (lit-[] f y₀)) Ay₀
ind-lit A f y₀ (lncons {i} {is} Ni LNis) Ay₀ ih =
  subst (λ t → A t)
        (sym (lit-∷ f i is y₀))
        (ih Ni (lit f is y₀) (ind-lit A f y₀ LNis Ay₀ ih))

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then totree(i, t) is ordered.
toTree-OrdTree : ∀ {item t} → N item → Tree t → OrdTree t →
                 OrdTree (toTree · item · t)
toTree-OrdTree {item} Nitem tnil _ =
  ordTree (toTree · item · nilTree)
    ≡⟨ subst (λ x → ordTree (toTree · item · nilTree) ≡
                    ordTree x)
             (toTree-nilTree item)
             refl
    ⟩
  ordTree (tip item)
    ≡⟨ ordTree-tip item ⟩
  true ∎

toTree-OrdTree {item} Nitem (ttip {i} Ni) _ =
  case prf₁ prf₂ (x>y∨x≤y Ni Nitem)
  where
  prf₁ : GT i item → OrdTree (toTree · item · tip i)
  prf₁ i>item =
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
    true && true && (item ≤ i) && ≤-ItemTree i (tip i)
      ≡⟨ subst (λ t → true && true && (item ≤ i) && ≤-ItemTree i (tip i) ≡
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
    true && true && true && (i ≤ i)
      ≡⟨ subst (λ t → true && true && true && (i ≤ i) ≡
                      true && true && true && t)
               (x≤x Ni)
               refl
      ⟩
    true && true && true && true
      ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
               (t&&x≡x true)
               refl
      ⟩
    true && true && true
      ≡⟨ subst (λ t → true && true && true ≡ true && t)
               (t&&x≡x true)
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

  prf₂ : LE i item → OrdTree (toTree · item · tip i)
  prf₂ i≤item =
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
               i≤item
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
    true && true && (i ≤ item) && ≤-ItemTree item (tip item)
      ≡⟨ subst (λ t → true && true && (i ≤ item) && ≤-ItemTree item (tip item) ≡
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
    true && true && true && (item ≤ item)
      ≡⟨ subst (λ t → true && true && true && (item ≤ item) ≡
                      true && true && true && t)
               (x≤x Nitem)
               refl
      ⟩
    true && true && true && true
      ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
               (t&&x≡x true)
               refl
      ⟩
    true && true && true
      ≡⟨ subst (λ t → true && true && true ≡ true && t) (t&&x≡x true) refl ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

toTree-OrdTree {item} Nitem (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTtnode =
  case prf₁ prf₂ (x>y∨x≤y Ni Nitem)
  where
  prf₁ : GT i item → OrdTree (toTree · item · node t₁ i t₂)
  prf₁ i>item =
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
               (toTree-OrdTree Nitem Tt₁
                               (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode))
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
               (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode)
               refl
      ⟩
    true && true && ≤-TreeItem (toTree · item · t₁) i && ≤-ItemTree i t₂
      ≡⟨ subst (λ t → true                              &&
                      true                              &&
                      ≤-TreeItem (toTree · item · t₁) i &&
                      ≤-ItemTree i t₂                   ≡
                      true && true && t && ≤-ItemTree i t₂)
               (toTree-OrdTree-helper₁ Ni Nitem i>item Tt₁
                 ((&&-list₄-t₃
                   (ordTree-Bool Tt₁)
                   (ordTree-Bool Tt₂)
                   (≤-TreeItem-Bool Tt₁ Ni)
                   (≤-ItemTree-Bool Ni Tt₂)
                   (trans (sym $ ordTree-node t₁ i t₂) OTtnode))))
               refl
      ⟩
    true && true && true && ≤-ItemTree i t₂
      ≡⟨ subst (λ t → true && true && true && ≤-ItemTree i t₂ ≡
                      true && true && true && t)
               (&&-list₄-t₄
                 (ordTree-Bool Tt₁)
                 (ordTree-Bool Tt₂)
                 (≤-TreeItem-Bool Tt₁ Ni)
                 (≤-ItemTree-Bool Ni Tt₂)
                 (trans (sym $ ordTree-node t₁ i t₂) OTtnode))
               refl
      ⟩
    true && true && true && true
      ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
               (t&&x≡x true)
               refl
      ⟩
    true && true && true
      ≡⟨ subst (λ t → true && true && true ≡ true && t) (t&&x≡x true) refl ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

  prf₂ : LE i item → OrdTree (toTree · item · node t₁ i t₂)
  prf₂ i≤item =
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
               (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode)
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
               (toTree-OrdTree Nitem Tt₂
                 (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTtnode))
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
               (&&-list₄-t₃
                 (ordTree-Bool Tt₁)
                 (ordTree-Bool Tt₂)
                 (≤-TreeItem-Bool Tt₁ Ni)
                 (≤-ItemTree-Bool Ni Tt₂)
                 (trans (sym $ ordTree-node t₁ i t₂) OTtnode))
               refl
      ⟩
    true && true && true && ≤-ItemTree i (toTree · item · t₂)
      ≡⟨ subst (λ t → true                              &&
                      true                              &&
                      true                              &&
                      ≤-ItemTree i (toTree · item · t₂) ≡
                      true && true && true && t)
               (toTree-OrdTree-helper₂ Ni Nitem i≤item Tt₂
                 ((&&-list₄-t₄
                   (ordTree-Bool Tt₁)
                     (ordTree-Bool Tt₂)
                     (≤-TreeItem-Bool Tt₁ Ni)
                     (≤-ItemTree-Bool Ni Tt₂)
                     (trans (sym $ ordTree-node t₁ i t₂) OTtnode))))
                 refl
      ⟩
    true && true && true && true
      ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
               (t&&x≡x true)
               refl
      ⟩
    true && true && true
      ≡⟨ subst (λ t → true && true && true ≡ true && t) (t&&x≡x true) refl ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

------------------------------------------------------------------------------
-- Burstall's lemma: ord(maketree(is)).

-- makeTree-TreeOrd : ∀ {is} → ListN is → OrdTree (makeTree is)
-- makeTree-TreeOrd LNis =
--   ind-lit OrdTree toTree nilTree LNis ordTree-nilTree
--           (λ Nx y TOy → toTree-OrdTree Nx {!!} TOy)

makeTree-OrdTree : ∀ {is} → ListN is → OrdTree (makeTree is)
makeTree-OrdTree lnnil =
  ordTree (lit toTree [] nilTree)
    ≡⟨ subst (λ t → ordTree (lit toTree [] nilTree) ≡ ordTree t)
             (lit-[] toTree nilTree)
             refl
    ⟩
  ordTree nilTree
    ≡⟨ ordTree-nilTree ⟩
  true ∎

makeTree-OrdTree (lncons {i} {is} Ni Lis) =
  ordTree (lit toTree (i ∷ is) nilTree)
    ≡⟨ subst (λ t → ordTree (lit toTree (i ∷ is) nilTree) ≡ ordTree t)
             (lit-∷ toTree i is nilTree)
             refl
    ⟩
  ordTree (toTree · i · (lit toTree is nilTree))
    ≡⟨ toTree-OrdTree Ni (makeTree-Tree Lis) (makeTree-OrdTree Lis) ⟩
  true ∎

------------------------------------------------------------------------------
-- Burstall's lemma: If ord(is1) and ord(is2) and is1 ≤ is2 then
-- ord(concat(is1, is2)).
++-OrdList : ∀ {is js} → ListN is → ListN js → OrdList is → OrdList js →
             LE-Lists is js → OrdList (is ++ js)

++-OrdList {js = js} lnnil LNjs LOis LOjs is≤js =
  subst (λ t → OrdList t) (sym $ ++-[] js) LOjs

++-OrdList {js = js} (lncons {i} {is} Ni LNis) LNjs LOi∷is LOjs i∷is≤js =
  subst (λ t → OrdList t) (sym $ ++-∷ i is js) lemma
  where
  lemma : OrdList (i ∷ is ++ js)
  lemma =
    ordList (i ∷ is ++ js)
      ≡⟨ ordList-∷ i (is ++ js) ⟩
    ≤-ItemList i (is ++ js) && ordList (is ++ js)
      ≡⟨ subst (λ t → ≤-ItemList i (is ++ js) && ordList (is ++ js) ≡
                      t && ordList (is ++ js))
               (++-OrdList-helper Ni LNis LNjs
                 (&&-list₂-t₁ (≤-ItemList-Bool Ni LNis)
                              (ordList-Bool LNis)
                              (trans (sym (ordList-∷ i is)) LOi∷is))
                 (&&-list₂-t₁ (≤-ItemList-Bool Ni LNjs)
                              (≤-Lists-Bool LNis LNjs)
                              (trans (sym (≤-Lists-∷ i is js)) i∷is≤js))
                 (&&-list₂-t₂ (≤-ItemList-Bool Ni LNjs)
                              (≤-Lists-Bool LNis LNjs)
                              (trans (sym (≤-Lists-∷ i is js)) i∷is≤js))
               )
               refl
      ⟩
    true && ordList (is ++ js)
      ≡⟨ subst (λ t → true && ordList (is ++ js) ≡ true && t)
               (++-OrdList LNis LNjs (subList-OrdList Ni LNis LOi∷is) LOjs
                           (&&-list₂-t₂
                             (≤-ItemList-Bool Ni LNjs)
                             (≤-Lists-Bool LNis LNjs)
                             (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)))
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

------------------------------------------------------------------------------
-- Burstall's lemma: If t is ordered then (flatten t) is ordered.
flatten-OrdList : ∀ {t} → Tree t → OrdTree t → OrdList (flatten t)
flatten-OrdList tnil OTt =
  subst (λ t → OrdList t) (sym flatten-nilTree) ordList-[]

flatten-OrdList (ttip {i} Ni) OTt =
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
    ≡⟨ t&&x≡x true ⟩
  true ∎

flatten-OrdList (tnode {t₁} {i} {t₂} Tt₁ Ni Tt₂) OTt =
  ordList (flatten (node t₁ i t₂))
    ≡⟨ subst (λ t → ordList (flatten (node t₁ i t₂)) ≡ ordList t)
             (flatten-node t₁ i t₂)
             refl
    ⟩
  ordList (flatten t₁ ++ flatten t₂)
    ≡⟨ ++-OrdList (flatten-ListN Tt₁)
                  (flatten-ListN Tt₂)
                  (flatten-OrdList Tt₁ (leftSubTree-OrdTree Tt₁ Ni Tt₂ OTt))
                  (flatten-OrdList Tt₂ (rightSubTree-OrdTree Tt₁ Ni Tt₂ OTt))
                  (flatten-OrdList-helper Tt₁ Ni Tt₂ OTt)
    ⟩
  true ∎
