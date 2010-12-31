------------------------------------------------------------------------------
-- Closures properties respect to OrdList
------------------------------------------------------------------------------

-- TODO
{-# OPTIONS --no-termination-check #-}

module LTC.Program.SortList.Properties.Closures.OrdListI where

open import LTC.Base

open import Common.Function using ( _$_ )
open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )

open import LTC.Data.Bool
  using ( _&&_ ; &&-tt
        ; Bool ; tB  -- The LTC booleans type.
        )
open import LTC.Data.Bool.PropertiesI
  using ( ≤-Bool
        ; &&-assoc
        ; &&-proj₁
        ; &&-proj₂
        ; &&₃-proj₁
        ; &&₃-proj₂
        ; &&₃-proj₃
        ; &&₃-proj₄
        ; &&-true₃
        ; &&-true₄
        )
open import LTC.Data.Nat.Inequalities using ( _≤_ ; LE )
open import LTC.Data.Nat.Inequalities.PropertiesI using ( ≤-trans )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )
open import LTC.Data.List using ( _++_ ; ++-[] ; ++-∷ )

open import LTC.Program.SortList.Properties.Closures.BoolI
  using ( ≤-ItemList-Bool
        ; ≤-ItemTree-Bool
        ; ≤-Lists-Bool
        ; ≤-TreeItem-Bool
        ; ordList-Bool
        ; ordTree-Bool
        )
open import LTC.Program.SortList.Properties.Closures.ListI
  using ( flatten-List )
open import LTC.Program.SortList.Properties.Closures.OrdTreeI
  using ( leftSubTree-OrdTree
        ; rightSubTree-OrdTree
        )
open import LTC.Program.SortList.Properties.MiscellaneousI
  using ( xs≤ys→xs≤zs→xs≤ys++zs
        ; xs≤zs→ys≤zs→xs++ys≤zs
        )
open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : {i : D} → N i → {is : D} → ListN is → OrdList (i ∷ is) →
                  OrdList is
subList-OrdList {i} Ni nilLN LOi∷is = ordList-[]

subList-OrdList {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js =
  &&-proj₂ (≤-ItemList-Bool Ni (consLN Nj Ljs))
           (ordList-Bool (consLN Nj Ljs))
           (trans (sym $ ordList-∷ i (j ∷ js)) LOi∷j∷js)

------------------------------------------------------------------------------
++-OrdList-aux : {item is js : D} → N item → ListN is → ListN js →
                 LE-ItemList item is →
                 LE-ItemList item js →
                 LE-Lists is js →
                 LE-ItemList item (is ++ js)
++-OrdList-aux {item} {js = js} _ nilLN _ _ item≤js _ =
  subst (λ t → LE-ItemList item t) (sym (++-[] js)) item≤js

++-OrdList-aux {item} {js = js} Nitem
               (consLN {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
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
               (&&-proj₁ (≤-Bool Nitem Ni)
                         (≤-ItemList-Bool Nitem LNis)
                         (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is))
               refl
      ⟩
    true && ≤-ItemList item (is ++ js)
      ≡⟨ subst (λ t → true && ≤-ItemList item (is ++ js) ≡ true && t)
               -- IH.
               (++-OrdList-aux Nitem LNis LNjs lemma₁ item≤js lemma₂)
               refl
      ⟩
    true && true ≡⟨ &&-tt ⟩
    true
  ∎
    where
      lemma₁ : ≤-ItemList item is ≡ true
      lemma₁ =  &&-proj₂ (≤-Bool Nitem Ni)
                         (≤-ItemList-Bool Nitem LNis)
                         (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is)


      lemma₂ : ≤-Lists is js ≡ true
      lemma₂ = &&-proj₂ (≤-ItemList-Bool Ni LNjs)
                        (≤-Lists-Bool LNis LNjs)
                        (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)

------------------------------------------------------------------------------
flatten-OrdList-aux : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ →
                      OrdTree (node t₁ i t₂) →
                      LE-Lists (flatten t₁) (flatten t₂)

flatten-OrdList-aux {t₂ = t₂} nilT Ni Tt₂ OTt =
  subst (λ t → LE-Lists t (flatten t₂))
        (sym (flatten-nilTree))
        (≤-Lists-[] (flatten t₂))

flatten-OrdList-aux (tipT {i₁} Ni₁) _ nilT OTt =
  begin
    ≤-Lists (flatten (tip i₁)) (flatten nilTree)
      ≡⟨ subst₂ (λ x₁ x₂ → ≤-Lists (flatten (tip i₁)) (flatten nilTree) ≡
                           ≤-Lists x₁ x₂)
                (flatten-tip i₁)
                flatten-nilTree
                refl
      ⟩
    ≤-Lists (i₁ ∷ []) []
      ≡⟨ ≤-Lists-∷ i₁ [] [] ⟩
    ≤-ItemList i₁ [] && ≤-Lists [] []
      ≡⟨ subst₂ (λ x₁ x₂ → ≤-ItemList i₁ [] && ≤-Lists [] [] ≡ x₁ && x₂ )
                (≤-ItemList-[] i₁)
                (≤-Lists-[] [])
                refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true
  ∎

flatten-OrdList-aux {i = i} (tipT {i₁} Ni₁) Ni (tipT {i₂} Ni₂) OTt =
  begin
    ≤-Lists (flatten (tip i₁)) (flatten (tip i₂))
      ≡⟨ subst₂ (λ x₁ x₂ → ≤-Lists (flatten (tip i₁)) (flatten (tip i₂)) ≡
                           ≤-Lists x₁ x₂)
                (flatten-tip i₁)
                (flatten-tip i₂)
                refl
      ⟩
    ≤-Lists (i₁ ∷ []) (i₂ ∷ [])
      ≡⟨ ≤-Lists-∷ i₁ [] (i₂ ∷ []) ⟩
    ≤-ItemList i₁ (i₂ ∷ []) && ≤-Lists [] (i₂ ∷ [])
      ≡⟨ subst (λ t → ≤-ItemList i₁ (i₂ ∷ []) && ≤-Lists [] (i₂ ∷ []) ≡
                      t && ≤-Lists [] (i₂ ∷ []))
               (≤-ItemList-∷ i₁ i₂ [])
               refl
      ⟩
    (i₁ ≤ i₂ && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ [])
      ≡⟨ subst (λ t → (i₁ ≤ i₂  && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ []) ≡
                      (t        && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ []))
               lemma
               refl
      ⟩
    (true && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ [])
      ≡⟨ subst₂ (λ x₁ x₂ → (true && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ []) ≡
                           (true && x₁)               && x₂)
                (≤-ItemList-[] i₁)
                (≤-Lists-[] (i₂ ∷ []))
                refl
      ⟩
    (true && true) && true
      ≡⟨ &&-assoc tB tB tB ⟩
    true && true && true
      ≡⟨ &&-true₃ ⟩
    true
  ∎
  where
    aux₁ : Bool (ordTree (tip i₁))
    aux₁ = ordTree-Bool (tipT Ni₁)

    aux₂ : Bool (ordTree (tip i₂))
    aux₂ = ordTree-Bool (tipT Ni₂)

    aux₃ : Bool (≤-TreeItem (tip i₁) i)
    aux₃ = ≤-TreeItem-Bool (tipT Ni₁) Ni

    aux₄ : Bool (≤-ItemTree i (tip i₂))
    aux₄ = ≤-ItemTree-Bool Ni (tipT Ni₂)

    aux₅ : ordTree (tip i₁) &&
           ordTree (tip i₂) &&
           ≤-TreeItem (tip i₁) i &&
           ≤-ItemTree i (tip i₂) ≡ true
    aux₅ = trans (sym (ordTree-node (tip i₁) i (tip i₂))) OTt

    lemma : LE i₁ i₂
    lemma = ≤-trans Ni₁ Ni Ni₂ i₁≤i i≤i₂
     where
       i₁≤i : LE i₁ i
       i₁≤i = trans (sym (≤-TreeItem-tip i₁ i))
                    (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

       i≤i₂ : LE i i₂
       i≤i₂ = trans (sym (≤-ItemTree-tip i i₂))
                    (&&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅)

flatten-OrdList-aux {i = i} (tipT {i1} Ni1) Ni
                    (nodeT {t21} {i2} {t22} Tt21 Ni2 Tt22) OTt =
  begin
    ≤-Lists (flatten (tip i1)) (flatten (node t21 i2 t22))
      ≡⟨ subst (λ x → ≤-Lists (flatten (tip i1)) (flatten (node t21 i2 t22)) ≡
                      ≤-Lists (flatten (tip i1)) x)
               (flatten-node t21 i2 t22)
               refl
      ⟩
    ≤-Lists (flatten (tip i1)) (flatten t21 ++ flatten t22)
      ≡⟨ xs≤ys→xs≤zs→xs≤ys++zs (flatten-List (tipT Ni1))
                               (flatten-List Tt21)
                               (flatten-List Tt22)
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (tipT Ni1)
    aux₂ = ordTree-Bool (nodeT Tt21 Ni2 Tt22)
    aux₃ = ≤-TreeItem-Bool (tipT Ni1) Ni
    aux₄ = ≤-ItemTree-Bool Ni (nodeT Tt21 Ni2 Tt22)
    aux₅ = trans (sym (ordTree-node (tip i1) i (node t21 i2 t22))) OTt

    -- Auxiliary terms to get the conjuncts from the fourth conjunct of OTt.
    aux₆ = ≤-ItemTree-Bool Ni Tt21
    aux₇ = ≤-ItemTree-Bool Ni Tt22
    aux₈ = trans (sym (≤-ItemTree-node i t21 i2 t22))
                 (&&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i1 : OrdTree (tip i1)
    OrdTree-tip-i1 = &&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-TreeItem-tip-i1-i : LE-TreeItem (tip i1) i
    LE-TreeItem-tip-i1-i = &&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten (tip i1)) (flatten t21)
    lemma₁ = flatten-OrdList-aux (tipT Ni1) Ni Tt21 OT  -- IH.
      where
        OrdTree-t21 : OrdTree t21
        OrdTree-t21 = leftSubTree-OrdTree Tt21 Ni2 Tt22
                                          (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t21 : LE-ItemTree i t21
        LE-ItemTree-i-t21 = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node (tip i1) i t21)
        OT =
          begin
            ordTree (node (tip i1) i t21)
              ≡⟨ ordTree-node (tip i1) i t21 ⟩
            ordTree (tip i1) &&
            ordTree t21 &&
            ≤-TreeItem (tip i1) i &&
            ≤-ItemTree i t21
              ≡⟨ subst₄ (λ w x y z → ordTree (tip i1) &&
                                     ordTree t21 &&
                                     ≤-TreeItem (tip i1) i &&
                                     ≤-ItemTree i t21 ≡
                                     w && x && y && z)
                        OrdTree-tip-i1
                        OrdTree-t21
                        LE-TreeItem-tip-i1-i
                        LE-ItemTree-i-t21
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten (tip i1)) (flatten t22)
    lemma₂ = flatten-OrdList-aux (tipT Ni1) Ni Tt22 OT  -- IH.
      where
        OrdTree-t22 : OrdTree t22
        OrdTree-t22 = rightSubTree-OrdTree Tt21 Ni2 Tt22
                                           (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t22 : LE-ItemTree i t22
        LE-ItemTree-i-t22 = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node (tip i1) i t22)
        OT =
          begin
            ordTree (node (tip i1) i t22)
              ≡⟨ ordTree-node (tip i1) i t22 ⟩
            ordTree (tip i1) &&
            ordTree t22 &&
            ≤-TreeItem (tip i1) i &&
            ≤-ItemTree i t22
              ≡⟨ subst₄ (λ w x y z → ordTree (tip i1) &&
                                     ordTree t22 &&
                                     ≤-TreeItem (tip i1) i &&
                                     ≤-ItemTree i t22 ≡
                                     w && x && y && z)
                        OrdTree-tip-i1
                        OrdTree-t22
                        LE-TreeItem-tip-i1-i
                        LE-ItemTree-i-t22
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

flatten-OrdList-aux {i = i} (nodeT {t11} {i1} {t12} Tt11 Ni1 Tt12) Ni nilT OTt =
  begin
    ≤-Lists (flatten (node t11 i1 t12)) (flatten nilTree)
      ≡⟨ subst (λ x → ≤-Lists (flatten (node t11 i1 t12)) (flatten nilTree) ≡
                      ≤-Lists x                           (flatten nilTree))
               (flatten-node t11 i1 t12 )
               refl
      ⟩
    ≤-Lists (flatten t11 ++  flatten t12) (flatten nilTree)
      ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-List Tt11)
                               (flatten-List Tt12)
                               (flatten-List nilT)
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (nodeT Tt11 Ni1 Tt12)
    aux₂ = ordTree-Bool nilT
    aux₃ = ≤-TreeItem-Bool (nodeT Tt11 Ni1 Tt12) Ni
    aux₄ = ≤-ItemTree-Bool Ni nilT
    aux₅ = trans (sym (ordTree-node (node t11 i1 t12) i nilTree )) OTt

    -- Auxiliary terms to get the conjuncts from the third conjunct of OTt.
    aux₆ = ≤-TreeItem-Bool Tt11 Ni
    aux₇ = ≤-TreeItem-Bool Tt12 Ni
    aux₈ = trans (sym (≤-TreeItem-node t11 i1 t12 i))
                 (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    LE-ItemTree-i-niltree : LE-ItemTree i nilTree
    LE-ItemTree-i-niltree = &&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten t11) (flatten nilTree)
    lemma₁ = flatten-OrdList-aux Tt11 Ni nilT OT  -- IH.
      where
        OrdTree-t11 : OrdTree t11
        OrdTree-t11 =
          leftSubTree-OrdTree Tt11 Ni1 Tt12
                              (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t11-i : LE-TreeItem t11 i
        LE-TreeItem-t11-i = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node t11 i nilTree)
        OT =
          begin
            ordTree (node t11 i nilTree )
              ≡⟨ ordTree-node t11 i nilTree ⟩
            ordTree t11 &&
            ordTree nilTree &&
            ≤-TreeItem t11 i &&
            ≤-ItemTree i nilTree
              ≡⟨ subst₄ (λ w x y z → ordTree t11 &&
                                     ordTree nilTree &&
                                     ≤-TreeItem t11 i &&
                                     ≤-ItemTree i nilTree ≡
                                     w && x && y && z)
                        OrdTree-t11
                        ordTree-nilTree
                        LE-TreeItem-t11-i
                        LE-ItemTree-i-niltree
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten t12) (flatten nilTree)
    lemma₂ = flatten-OrdList-aux Tt12 Ni nilT OT  -- IH.
      where
        OrdTree-t12 : OrdTree t12
        OrdTree-t12 =
          rightSubTree-OrdTree Tt11 Ni1 Tt12 (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t12-i : LE-TreeItem t12 i
        LE-TreeItem-t12-i = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node t12 i nilTree)
        OT =
          begin
            ordTree (node t12 i nilTree )
              ≡⟨ ordTree-node t12 i nilTree ⟩
            ordTree t12 &&
            ordTree nilTree &&
            ≤-TreeItem t12 i &&
            ≤-ItemTree i nilTree
              ≡⟨ subst₄ (λ w x y z → ordTree t12 &&
                                     ordTree nilTree &&
                                     ≤-TreeItem t12 i &&
                                     ≤-ItemTree i nilTree ≡
                                     w && x && y && z)
                        OrdTree-t12
                        ordTree-nilTree
                        LE-TreeItem-t12-i
                        LE-ItemTree-i-niltree
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

flatten-OrdList-aux {i = i} (nodeT {t11} {i1} {t12} Tt11 Ni1 Tt12) Ni
                    (tipT {i2} Ni2) OTt =
  begin
    ≤-Lists (flatten (node t11 i1 t12)) (flatten (tip i2))
      ≡⟨ subst (λ x → ≤-Lists (flatten (node t11 i1 t12)) (flatten (tip i2)) ≡
                      ≤-Lists x                           (flatten (tip i2)))
               (flatten-node t11 i1 t12 )
               refl
      ⟩
    ≤-Lists (flatten t11 ++  flatten t12) (flatten (tip i2))
      ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-List Tt11)
                               (flatten-List Tt12)
                               (flatten-List (tipT Ni2))
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (nodeT Tt11 Ni1 Tt12)
    aux₂ = ordTree-Bool (tipT Ni2)
    aux₃ = ≤-TreeItem-Bool (nodeT Tt11 Ni1 Tt12) Ni
    aux₄ = ≤-ItemTree-Bool Ni (tipT Ni2)
    aux₅ = trans (sym (ordTree-node (node t11 i1 t12) i (tip i2))) OTt

    -- Auxiliary terms to get the conjuncts from the third conjunct of OTt.
    aux₆ = ≤-TreeItem-Bool Tt11 Ni
    aux₇ = ≤-TreeItem-Bool Tt12 Ni
    aux₈ = trans (sym (≤-TreeItem-node t11 i1 t12 i))
                 (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i2 : OrdTree (tip i2)
    OrdTree-tip-i2 = &&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-ItemTree-i-tip-i2 : LE-ItemTree i (tip i2)
    LE-ItemTree-i-tip-i2 = &&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten t11) (flatten (tip i2))
    lemma₁ = flatten-OrdList-aux Tt11 Ni (tipT Ni2) OT  -- IH.
      where
        OrdTree-t11 : OrdTree t11
        OrdTree-t11 =
          leftSubTree-OrdTree Tt11 Ni1 Tt12 (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t11-i : LE-TreeItem t11 i
        LE-TreeItem-t11-i = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node t11 i (tip i2))
        OT =
          begin
            ordTree (node t11 i (tip i2) )
              ≡⟨ ordTree-node t11 i (tip i2) ⟩
            ordTree t11 &&
            ordTree (tip i2) &&
            ≤-TreeItem t11 i &&
            ≤-ItemTree i (tip i2)
              ≡⟨ subst₄ (λ w x y z → ordTree t11 &&
                                     ordTree (tip i2) &&
                                     ≤-TreeItem t11 i &&
                                     ≤-ItemTree i (tip i2) ≡
                                     w && x && y && z)
                        OrdTree-t11
                        OrdTree-tip-i2
                        LE-TreeItem-t11-i
                        LE-ItemTree-i-tip-i2
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten t12) (flatten (tip i2))
    lemma₂ = flatten-OrdList-aux Tt12 Ni (tipT Ni2) OT  -- IH.
      where
        OrdTree-t12 : OrdTree t12
        OrdTree-t12 =
          rightSubTree-OrdTree Tt11 Ni1 Tt12 (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t12-i : LE-TreeItem t12 i
        LE-TreeItem-t12-i = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node t12 i (tip i2))
        OT =
          begin
            ordTree (node t12 i (tip i2) )
              ≡⟨ ordTree-node t12 i (tip i2) ⟩
            ordTree t12 &&
            ordTree (tip i2) &&
            ≤-TreeItem t12 i &&
            ≤-ItemTree i (tip i2)
              ≡⟨ subst₄ (λ w x y z → ordTree t12 &&
                                     ordTree (tip i2) &&
                                     ≤-TreeItem t12 i &&
                                     ≤-ItemTree i (tip i2) ≡
                                     w && x && y && z)
                        OrdTree-t12
                        OrdTree-tip-i2
                        LE-TreeItem-t12-i
                        LE-ItemTree-i-tip-i2
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

flatten-OrdList-aux {i = i} (nodeT {t11} {i1} {t12} Tt11 Ni1 Tt12) Ni
                    (nodeT {t21} {i2} {t22} Tt21 Ni2 Tt22) OTt =
  begin
    ≤-Lists (flatten (node t11 i1 t12)) (flatten (node t21 i2 t22))
      ≡⟨ subst (λ x → ≤-Lists (flatten (node t11 i1 t12))
                              (flatten (node t21 i2 t22)) ≡
                      ≤-Lists x (flatten (node t21 i2 t22)))
               (flatten-node t11 i1 t12 )
               refl
      ⟩
    ≤-Lists (flatten t11 ++  flatten t12) (flatten (node t21 i2 t22))
      ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-List Tt11)
                               (flatten-List Tt12)
                               (flatten-List (nodeT Tt21 Ni2 Tt22))
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (nodeT Tt11 Ni1 Tt12)
    aux₂ = ordTree-Bool (nodeT Tt21 Ni2 Tt22)
    aux₃ = ≤-TreeItem-Bool (nodeT Tt11 Ni1 Tt12) Ni
    aux₄ = ≤-ItemTree-Bool Ni (nodeT Tt21 Ni2 Tt22)
    aux₅ = trans (sym (ordTree-node (node t11 i1 t12) i (node t21 i2 t22))) OTt

    -- Auxiliary terms to get the conjuncts from the third conjunct of OTt.
    aux₆ = ≤-TreeItem-Bool Tt11 Ni
    aux₇ = ≤-TreeItem-Bool Tt12 Ni
    aux₈ = trans (sym (≤-TreeItem-node t11 i1 t12 i))
                 (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-node-t21-i2-t22 : OrdTree (node t21 i2 t22)
    OrdTree-node-t21-i2-t22 = &&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-ItemTree-i-node-t21-i2-t22 : LE-ItemTree i (node t21 i2 t22)
    LE-ItemTree-i-node-t21-i2-t22 = &&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten t11) (flatten (node t21 i2 t22))
    lemma₁ = flatten-OrdList-aux Tt11 Ni (nodeT Tt21 Ni2 Tt22) OT  -- IH.
      where
        OrdTree-t11 : OrdTree t11
        OrdTree-t11 =
          leftSubTree-OrdTree Tt11 Ni1 Tt12 (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t11-i : LE-TreeItem t11 i
        LE-TreeItem-t11-i = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node t11 i (node t21 i2 t22))
        OT =
          begin
            ordTree (node t11 i (node t21 i2 t22) )
              ≡⟨ ordTree-node t11 i (node t21 i2 t22) ⟩
            ordTree t11 &&
            ordTree (node t21 i2 t22) &&
            ≤-TreeItem t11 i &&
            ≤-ItemTree i (node t21 i2 t22)
              ≡⟨ subst₄ (λ w x y z → ordTree t11 &&
                                     ordTree (node t21 i2 t22) &&
                                     ≤-TreeItem t11 i &&
                                     ≤-ItemTree i (node t21 i2 t22) ≡
                                     w && x && y && z)
                        OrdTree-t11
                        OrdTree-node-t21-i2-t22
                        LE-TreeItem-t11-i
                        LE-ItemTree-i-node-t21-i2-t22
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten t12) (flatten (node t21 i2 t22))
    lemma₂ = flatten-OrdList-aux Tt12 Ni (nodeT Tt21 Ni2 Tt22) OT  -- IH.
      where
        OrdTree-t12 : OrdTree t12
        OrdTree-t12 =
          rightSubTree-OrdTree Tt11 Ni1 Tt12 (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t12-i : LE-TreeItem t12 i
        LE-TreeItem-t12-i = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node t12 i (node t21 i2 t22))
        OT =
          begin
            ordTree (node t12 i (node t21 i2 t22) )
              ≡⟨ ordTree-node t12 i (node t21 i2 t22) ⟩
            ordTree t12 &&
            ordTree (node t21 i2 t22) &&
            ≤-TreeItem t12 i &&
            ≤-ItemTree i (node t21 i2 t22)
              ≡⟨ subst₄ (λ w x y z → ordTree t12 &&
                                     ordTree (node t21 i2 t22) &&
                                     ≤-TreeItem t12 i &&
                                     ≤-ItemTree i (node t21 i2 t22) ≡
                                     w && x && y && z)
                        OrdTree-t12
                        OrdTree-node-t21-i2-t22
                        LE-TreeItem-t12-i
                        LE-ItemTree-i-node-t21-i2-t22
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎
