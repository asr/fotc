------------------------------------------------------------------------------
-- Closures properties respect to ListOrd (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.ListOrdER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.Closures.BoolER
  using ( ≤-ItemList-Bool ; ≤-Lists-Bool ; isListOrd-Bool)
open import Examples.SortList.Closures.TreeOrdER
  using ( leftSubTree-TreeOrd ; rightSubTree-TreeOrd )
open import Examples.SortList.Properties using ( subList-ListOrd )
open import Examples.SortList.SortList

open import LTC.Data.Bool
open import LTC.Data.Bool.PropertiesER using
  ( ≤-Bool ; x&&y≡true→x≡true ; x&&y≡true→y≡true )
open import LTC.Data.Nat.Inequalities
-- open import LTC.Data.Nat.Inequalities.PropertiesER using ( ≤-trans )
open import LTC.Data.Nat.List.Type
open import LTC.Data.Nat.Type
open import LTC.Data.List

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

-- -- If t is ordered then (flatten t) is ordered
-- flatten-ListOrd : {t : D} → Tree t → TreeOrd t → ListOrd (flatten t)
-- flatten-ListOrd nilT TOnilT = prf
--   where
--     postulate prf : ListOrd (flatten nilTree)
--     {-# ATP prove prf #-}

-- flatten-ListOrd (tipT {i} Ni ) TOtipT = prf
--   where
--     postulate prf : ListOrd (flatten (tip i))
--     {-# ATP prove prf #-}

-- flatten-ListOrd (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂ ) TOnodeT =
--   prf (flatten-ListOrd Tt₁ (leftSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT))
--       (flatten-ListOrd Tt₂ (rightSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT))
--       (flatten-ListOrd-aux Tt₁ Ni Tt₂ TOnodeT)
--   where

--     postulate prf : ListOrd (flatten t₁) → -- IH.
--                     ListOrd (flatten t₂) → -- IH.
--                     ≤-Lists (flatten t₁) (flatten t₂) ≡ true →
--                     ListOrd (flatten (node t₁ i t₂))
--     {-# ATP prove prf ++-ListOrd flatten-List
--                   leftSubTree-TreeOrd rightSubTree-TreeOrd
--     #-}

--     flatten-ListOrd-aux : {taux₁ iaux taux₂ : D} → Tree taux₁ → N iaux →
--                           Tree taux₂ → TreeOrd (node taux₁ iaux taux₂) →
--                           ≤-Lists (flatten taux₁) (flatten taux₂) ≡ true
--     flatten-ListOrd-aux {taux₂ = taux₂} nilT Niaux Ttaux₂ _ = prf-aux
--       where
--         postulate prf-aux : ≤-Lists (flatten nilTree) (flatten taux₂) ≡ true
--         {-# ATP prove prf-aux #-}

--     flatten-ListOrd-aux (tipT {j} Nj) Niaux nilT TOaux = prf-aux
--       where
--         postulate prf-aux : ≤-Lists (flatten (tip j)) (flatten nilTree) ≡ true
--         {-# ATP prove prf-aux #-}

--     flatten-ListOrd-aux (tipT {j} Nj) Niaux (tipT {k} Nk) TOaux = prf-aux
--       where
--         postulate prf-aux : ≤-Lists (flatten (tip j)) (flatten (tip k)) ≡ true
--         {-# ATP prove prf-aux #-}

--     flatten-ListOrd-aux (tipT {j} Nj) Niaux (nodeT {ta} {k} {tb} Tta Nk Ttb )
--                         TOaux = prf-aux
--       where
--         postulate prf-aux : ≤-Lists (flatten (tip j)) (flatten (node ta k tb)) ≡
--                             true
--         {-# ATP prove prf-aux #-}

--     flatten-ListOrd-aux (nodeT {ta} {j} {tb} Tta Nj Ttb) Niaux nilT TOaux =
--       prf-aux (flatten-List (nodeT Tta Nj Ttb))
--               (flatten-ListOrd (nodeT Tta Nj Ttb)
--               (leftSubTree-TreeOrd (nodeT Tta Nj Ttb) Niaux nilT TOaux))
--       where
--         postulate prf-aux : List (flatten (node ta j tb)) →
--                             ListOrd (flatten (node ta j tb)) → --IH.
--                             ≤-Lists (flatten (node ta j tb)) (flatten nilTree) ≡
--                             true
--         {-# ATP prove prf-aux xs≤[] #-}

--     flatten-ListOrd-aux (nodeT {ta} {j} {tb} Tta Nj Ttb) Niaux (tipT {k} Nk)
--                         TOaux = prf-aux
--       where
--         postulate prf-aux : ≤-Lists (flatten (node ta j tb)) (flatten (tip k)) ≡
--                             true
--         {-# ATP prove prf-aux #-}

--       -- begin
--       --   ≤-Lists (flatten (node ta j tb)) (flatten (tip k))
--       --     ≡⟨ {!!} ⟩
--       --   {!≤-Lists (flatten (tip k)!}
--       --   ≡⟨ {!!} ⟩
--       --   {!!} ≡⟨ {!!} ⟩
--       --   true
--       -- ∎

--     flatten-ListOrd-aux (nodeT {ta} {j} {tb} Tta Nj Ttb) Niaux
--                         (nodeT {tc} {k} {td} Ttc Nk Ttd) TOaux = prf-aux
--                         where
--                         postulate prf-aux : ≤-Lists (flatten (node ta j tb))
--                                             (flatten (node tc k td)) ≡ true
