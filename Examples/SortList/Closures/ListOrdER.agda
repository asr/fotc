------------------------------------------------------------------------------
-- Closures properties respect to ListOrd (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.ListOrdER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

open import Examples.SortList.Closures.BoolER using
  ( ≤-ItemList-Bool
  ; ≤-Lists-Bool
  ; isListOrd-Bool
  )
open import Examples.SortList.Closures.TreeOrdER using
  ( leftSubTree-TreeOrd
  ; rightSubTree-TreeOrd
  )
open import Examples.SortList.Properties using ( subList-ListOrd )
open import Examples.SortList.SortList using
  ( ≤-ItemList ; ≤-ItemList-∷
  ; ≤-Lists ; ≤-Lists-∷
  ; flatten
  ; LE-ItemList
  ; LE-Lists
  ; ListOrd
  ; isListOrd ; isListOrd-∷
  ; Tree
  ; TreeOrd
  )

open import LTC.Data.Bool using ( _&&_ ; &&-tt )
open import LTC.Data.Bool.PropertiesER using
  ( ≤-Bool
  ; x&&y≡true→x≡true
  ; x&&y≡true→y≡true
  )
open import LTC.Data.Nat.Inequalities using ( _≤_ )
open import LTC.Data.Nat.List.Type using
  ( ListN ; consLN ; nilLN -- The LTC list of natural numbers type
  )
open import LTC.Data.Nat.Type using ( N )
open import LTC.Data.List using ( _++_ ; ++-[] ; ++-∷ )

import MyStdLib.Relation.Binary.EqReasoning
open module ListOrd-ER =
  MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

open import Postulates using ( ++-ListOrd-aux₁ )

------------------------------------------------------------------------------
-- Auxiliar functions

-- ++-ListOrd-aux₁ : {item is js : D} → N item → List is → List js →
--                   LE-ItemList item is →
--                   LE-Lists is js →
--                   LE-ItemList item js
-- ++-ListOrd-aux₁ {item} Nitem LNis  nilL item≤is is≤js = ≤-ItemList-[] item
-- ++-ListOrd-aux₁ {item} Nitem nilL (consL {j} {js} Nj Njs LNjs)
--                 item≤nilL nilL≤j∷js =
--   begin
--      ≤-ItemList item (j ∷ js)
--        ≡⟨ ≤-ItemList-∷ item j js ⟩
--      item ≤ j && ≤-ItemList item js
--        ≡⟨ subst (λ t → item ≤ j && ≤-ItemList item js ≡
--                        t && ≤-ItemList item js)
--                 --
--                 {!!}
--                 refl
--        ⟩
--      true && ≤-ItemList item js ≡⟨ {!!} ⟩
--      {!!} ≡⟨ {!!} ⟩

--     true
--   ∎

-- ++-ListOrd-aux₁ {item} Nitem (consL {i} {is} Ni Nis Lis)
--                 (consL {j} {js} Nj Njs LNjs) item≤i∷is i∷is≤j∷js =
--       -- IH
--       ++-ListOrd-aux₁ Nitem Lis (consL Nj Njs LNjs)
--           (x&&y≡true→y≡true (≤-Bool Nitem Ni)
--                             (≤-ItemList-Bool Nitem Lis)
--                             (trans (sym (≤-ItemList-∷ item i is)) item≤i∷is))
--           (x&&y≡true→y≡true (≤-ItemList-Bool Ni Lis)
--                             (≤-Lists-Bool LNis (consL Nj Njs LNjs))
--                             (trans (sym (≤-Lists-∷ i is (j ∷ js))) i∷is≤j∷js))

++-ListOrd-aux₂ : {item is js : D} → N item → ListN is → ListN js →
                 LE-ItemList item is →
                 LE-Lists is js →
                 LE-ItemList item (is ++ js)
++-ListOrd-aux₂ {item} {js = js} Nitem nilLN LNjs item≤niL niL≤js =
  ++-ListOrd-aux₁ Nitem nilLN (subst (λ t → ListN t)
      (sym (++-[] js)) LNjs) item≤niL
      ( begin
          ≤-Lists [] ([] ++ js)
            ≡⟨ subst (λ t → ≤-Lists [] ([] ++ js) ≡ ≤-Lists [] t)
                     (++-[] js)
                     refl
            ⟩
          ≤-Lists [] js
          ≡⟨ niL≤js ⟩
          true
        ∎
      )

++-ListOrd-aux₂ {item} {js = js} Nitem
               (consLN {i} {is} Ni LNis) LNjs item≤i∷is i∷is≤js =
  begin
    ≤-ItemList item ((i ∷ is) ++ js)
      ≡⟨ subst (λ t → ≤-ItemList item ((i ∷ is) ++ js) ≡ ≤-ItemList item t)
               (++-∷ i is js)
               refl
      ⟩
    ≤-ItemList item (i ∷ (is ++ js))
      ≡⟨ ≤-ItemList-∷ item i (is ++ js) ⟩
    item ≤ i && ≤-ItemList item (is ++ js)
      ≡⟨ subst (λ t → item ≤ i && ≤-ItemList item (is ++ js) ≡
                      t && ≤-ItemList item (is ++ js))
               (x&&y≡true→x≡true (≤-Bool Nitem Ni)
                                 (≤-ItemList-Bool Nitem LNis)
                                 (trans (sym (≤-ItemList-∷ item i is))
                                        item≤i∷is))
               refl
      ⟩
    true && ≤-ItemList item (is ++ js)
      ≡⟨ subst (λ t → true && ≤-ItemList item (is ++ js) ≡ true && t)
               -- IH.
               (++-ListOrd-aux₂ Nitem LNis LNjs
                 (x&&y≡true→y≡true (≤-Bool Nitem Ni)
                                   (≤-ItemList-Bool Nitem LNis)
                                   (trans (sym (≤-ItemList-∷ item i is))
                                          item≤i∷is))
               (x&&y≡true→y≡true (≤-ItemList-Bool Ni LNis)
                                 (≤-Lists-Bool LNis LNjs)
                                 (trans (sym (≤-Lists-∷ i is js)) i∷is≤js)))
               refl
      ⟩
    true && true ≡⟨ &&-tt ⟩
    true
  ∎

------------------------------------------------------------------------------
-- Append preserves the order.
++-ListOrd : {is js : D} → ListN is → ListN js → ListOrd is → ListOrd js →
         LE-Lists is js → ListOrd (is ++ js)

++-ListOrd {js = js} nilLN LNjs LOis LOjs is≤js =
  subst (λ t → ListOrd t) (sym (++-[] js)) LOjs

++-ListOrd {js = js} (consLN {i} {is} Ni LNis) LNjs LOi∷is LOjs i∷is≤js =
  subst (λ t → ListOrd t)
        (sym (++-∷ i is js))
        ( begin
            isListOrd (i ∷ is ++ js)
              ≡⟨ isListOrd-∷ i (is ++ js) ⟩
            ≤-ItemList i (is ++ js) && isListOrd (is ++ js)
              ≡⟨ subst (λ t → ≤-ItemList i (is ++ js) &&
                              isListOrd (is ++ js)    ≡
                              t                       &&
                              isListOrd (is ++ js))
                       (++-ListOrd-aux₂ Ni LNis LNjs
                           (x&&y≡true→x≡true (≤-ItemList-Bool Ni LNis)
                                             (≤-Lists-Bool LNis LNjs)
                                             (trans (sym (≤-Lists-∷ i is js))
                                                    i∷is≤js))
                           (x&&y≡true→y≡true (≤-ItemList-Bool Ni LNis)
                                             (≤-Lists-Bool LNis LNjs)
                                             (trans (sym (≤-Lists-∷ i is js))
                                                    i∷is≤js)))
                       refl
              ⟩
            true && isListOrd (is ++ js)
            ≡⟨ subst (λ t → true && isListOrd (is ++ js) ≡ true && t)
                     -- IH.
                     (++-ListOrd LNis LNjs (subList-ListOrd Ni LNis LOi∷is) LOjs
                             (x&&y≡true→y≡true
                               (≤-ItemList-Bool Ni LNis)
                               (≤-Lists-Bool LNis LNjs)
                               (trans (sym (≤-Lists-∷ i is js)) i∷is≤js)))
                     refl
            ⟩
            true && true
              ≡⟨ &&-tt ⟩
            true
          ∎
        )

------------------------------------------------------------------------------
-- If t is ordered then (flatten t) is ordered.
-- See the ATP version.
postulate
  flatten-ListOrd : {t : D} → Tree t → TreeOrd t → ListOrd (flatten t)

-- treeOrd-tb-i-k : TreeOrd (node tb i (tip k))
-- treeOrd-tb-i-k =
--   begin
--     isTreeOrd (node tb i (tip k))
--       ≡⟨ isTreeOrd-node tb i (tip k) ⟩
--     isTreeOrd tb && isTreeOrd (tip k) && ≤-TreeItem tb i && ≤-ItemTree i (tip k)
--       ≡⟨ subst (λ t → isTreeOrd tb        &&
--                       isTreeOrd (tip k)   &&
--                       ≤-TreeItem tb i     &&
--                       ≤-ItemTree i (tip k) ≡
--                       t                   &&
--                       isTreeOrd (tip k)   &&
--                       ≤-TreeItem tb i     &&
--                       ≤-ItemTree i (tip k))
--                (rightSubTree-TreeOrd Tta Nj Ttb aux)
--                refl
--       ⟩
--     true && isTreeOrd (tip k) && ≤-TreeItem tb i && ≤-ItemTree i (tip k)
--       ≡⟨ subst (λ t → true &&
--                       isTreeOrd (tip k) &&
--                       ≤-TreeItem tb i &&
--                       ≤-ItemTree i (tip k) ≡
--                       true &&
--                       t &&
--                       ≤-TreeItem tb i &&
--                       ≤-ItemTree i (tip k))
--                (isTreeOrd-tip k)
--                refl
--       ⟩
--     true && true && ≤-TreeItem tb i && ≤-ItemTree i (tip k)
--       ≡⟨ subst (λ t → true && true && ≤-TreeItem tb i && ≤-ItemTree i (tip k) ≡
--                       true && true && t && ≤-ItemTree i (tip k))
--                (x&&y≡true→y≡true (≤-TreeItem-Bool Tta Ni)
--                                  (≤-TreeItem-Bool Ttb Ni)
--                                  (trans (sym (≤-TreeItem-node ta j tb i))
--                                    (w&&x&&y&&z≡true→y≡true
--                                      (isTreeOrd-Bool (nodeT Tta Nj Ttb))
--                                        (isTreeOrd-Bool (tipT Nk))
--                                        (≤-TreeItem-Bool (nodeT Tta Nj Ttb) Ni)
--                                        (≤-ItemTree-Bool Ni (tipT Nk))
--                                        (trans (sym (isTreeOrd-node
--                                                    (node ta j tb)
--                                                    i (tip k)))
--                                               TOnode))))
--                refl
--       ⟩
--     true && true && true && ≤-ItemTree i (tip k)
--       ≡⟨ subst (λ t → true && true && true && ≤-ItemTree i (tip k) ≡
--                       true && true && true && t)
--                (w&&x&&y&&z≡true→z≡true
--                  (isTreeOrd-Bool (nodeT Tta Nj Ttb))
--                  (isTreeOrd-Bool (tipT Nk))
--                  (≤-TreeItem-Bool (nodeT Tta Nj Ttb) Ni)
--                  (≤-ItemTree-Bool Ni (tipT Nk))
--                  (trans (sym (isTreeOrd-node (node ta j tb) i (tip k)))
--                         TOnode))
--          refl
--       ⟩
--     true && true && true && true
--       ≡⟨ subst (λ t → true && true && true && true ≡ true && true && t)
--                &&-tt
--                refl
--       ⟩
--     true && true && true
--       ≡⟨ subst (λ t → true && true && true ≡ true && t)
--                &&-tt
--                refl
--       ⟩
--     true && true
--          ≡⟨ &&-tt ⟩
--     true
--   ∎
