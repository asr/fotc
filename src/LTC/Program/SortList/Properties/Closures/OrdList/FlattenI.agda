------------------------------------------------------------------------------
-- Closures properties respect to OrdList (flatten-OrdList-aux)
------------------------------------------------------------------------------

-- Agda bug? The recursive calls in flatten-OrdList-aux are
-- structurally smaller, so it is not clear why we need the option
-- --no-termination-check. We tested the option --termination-depth=N
-- with some values, but it had no effect.
{-# OPTIONS --no-termination-check #-}

module LTC.Program.SortList.Properties.Closures.OrdList.FlattenI where

open import LTC.Base

-- open import Common.Function

open import LTC.Data.Bool
open import LTC.Data.Bool.PropertiesI
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesI
open import LTC.Data.Nat.Type
open import LTC.Data.List

open import LTC.Program.SortList.Properties.Closures.BoolI
open import LTC.Program.SortList.Properties.Closures.ListN-I
open import LTC.Program.SortList.Properties.Closures.OrdTreeI
open import LTC.Program.SortList.Properties.MiscellaneousI
open import LTC.Program.SortList.SortList

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

flatten-OrdList-aux : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
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

flatten-OrdList-aux {i = i} (tipT {i₁} Ni₁) Ni
                    (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt =
  begin
    ≤-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂))
      ≡⟨ subst (λ x → ≤-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂)) ≡
                      ≤-Lists (flatten (tip i₁)) x)
               (flatten-node t₂₁ i₂ t₂₂)
               refl
      ⟩
    ≤-Lists (flatten (tip i₁)) (flatten t₂₁ ++ flatten t₂₂)
      ≡⟨ xs≤ys→xs≤zs→xs≤ys++zs (flatten-ListN (tipT Ni₁))
                               (flatten-ListN Tt₂₁)
                               (flatten-ListN Tt₂₂)
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (tipT Ni₁)
    aux₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
    aux₃ = ≤-TreeItem-Bool (tipT Ni₁) Ni
    aux₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
    aux₅ = trans (sym (ordTree-node (tip i₁) i (node t₂₁ i₂ t₂₂))) OTt

    -- Auxiliary terms to get the conjuncts from the fourth conjunct of OTt.
    aux₆ = ≤-ItemTree-Bool Ni Tt₂₁
    aux₇ = ≤-ItemTree-Bool Ni Tt₂₂
    aux₈ = trans (sym (≤-ItemTree-node i t₂₁ i₂ t₂₂))
                 (&&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i₁ : OrdTree (tip i₁)
    OrdTree-tip-i₁ = &&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-TreeItem-tip-i₁-i : LE-TreeItem (tip i₁) i
    LE-TreeItem-tip-i₁-i = &&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten (tip i₁)) (flatten t₂₁)
    lemma₁ = flatten-OrdList-aux (tipT Ni₁) Ni Tt₂₁ OT  -- IH.
      where
        OrdTree-t₂₁ : OrdTree t₂₁
        OrdTree-t₂₁ = leftSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                                          (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t₂₁ : LE-ItemTree i t₂₁
        LE-ItemTree-i-t₂₁ = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node (tip i₁) i t₂₁)
        OT =
          begin
            ordTree (node (tip i₁) i t₂₁)
              ≡⟨ ordTree-node (tip i₁) i t₂₁ ⟩
            ordTree (tip i₁) &&
            ordTree t₂₁ &&
            ≤-TreeItem (tip i₁) i &&
            ≤-ItemTree i t₂₁
              ≡⟨ subst₄ (λ w x y z → ordTree (tip i₁) &&
                                     ordTree t₂₁ &&
                                     ≤-TreeItem (tip i₁) i &&
                                     ≤-ItemTree i t₂₁ ≡
                                     w && x && y && z)
                        OrdTree-tip-i₁
                        OrdTree-t₂₁
                        LE-TreeItem-tip-i₁-i
                        LE-ItemTree-i-t₂₁
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten (tip i₁)) (flatten t₂₂)
    lemma₂ = flatten-OrdList-aux (tipT Ni₁) Ni Tt₂₂ OT  -- IH.
      where
        OrdTree-t₂₂ : OrdTree t₂₂
        OrdTree-t₂₂ = rightSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                                           (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t₂₂ : LE-ItemTree i t₂₂
        LE-ItemTree-i-t₂₂ = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node (tip i₁) i t₂₂)
        OT =
          begin
            ordTree (node (tip i₁) i t₂₂)
              ≡⟨ ordTree-node (tip i₁) i t₂₂ ⟩
            ordTree (tip i₁) &&
            ordTree t₂₂ &&
            ≤-TreeItem (tip i₁) i &&
            ≤-ItemTree i t₂₂
              ≡⟨ subst₄ (λ w x y z → ordTree (tip i₁) &&
                                     ordTree t₂₂ &&
                                     ≤-TreeItem (tip i₁) i &&
                                     ≤-ItemTree i t₂₂ ≡
                                     w && x && y && z)
                        OrdTree-tip-i₁
                        OrdTree-t₂₂
                        LE-TreeItem-tip-i₁-i
                        LE-ItemTree-i-t₂₂
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

flatten-OrdList-aux {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni nilT OTt =
  begin
    ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nilTree)
      ≡⟨ subst (λ x → ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nilTree) ≡
                      ≤-Lists x                           (flatten nilTree))
               (flatten-node t₁₁ i₁ t₁₂ )
               refl
      ⟩
    ≤-Lists (flatten t₁₁ ++  flatten t₁₂) (flatten nilTree)
      ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-ListN Tt₁₁)
                               (flatten-ListN Tt₁₂)
                               (flatten-ListN nilT)
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
    aux₂ = ordTree-Bool nilT
    aux₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
    aux₄ = ≤-ItemTree-Bool Ni nilT
    aux₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i nilTree )) OTt

    -- Auxiliary terms to get the conjuncts from the third conjunct of OTt.
    aux₆ = ≤-TreeItem-Bool Tt₁₁ Ni
    aux₇ = ≤-TreeItem-Bool Tt₁₂ Ni
    aux₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                 (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    LE-ItemTree-i-niltree : LE-ItemTree i nilTree
    LE-ItemTree-i-niltree = &&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten t₁₁) (flatten nilTree)
    lemma₁ = flatten-OrdList-aux Tt₁₁ Ni nilT OT  -- IH.
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂
                              (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t₁₁-i : LE-TreeItem t₁₁ i
        LE-TreeItem-t₁₁-i = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node t₁₁ i nilTree)
        OT =
          begin
            ordTree (node t₁₁ i nilTree )
              ≡⟨ ordTree-node t₁₁ i nilTree ⟩
            ordTree t₁₁ &&
            ordTree nilTree &&
            ≤-TreeItem t₁₁ i &&
            ≤-ItemTree i nilTree
              ≡⟨ subst₄ (λ w x y z → ordTree t₁₁ &&
                                     ordTree nilTree &&
                                     ≤-TreeItem t₁₁ i &&
                                     ≤-ItemTree i nilTree ≡
                                     w && x && y && z)
                        OrdTree-t₁₁
                        ordTree-nilTree
                        LE-TreeItem-t₁₁-i
                        LE-ItemTree-i-niltree
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten t₁₂) (flatten nilTree)
    lemma₂ = flatten-OrdList-aux Tt₁₂ Ni nilT OT  -- IH.
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t₁₂-i : LE-TreeItem t₁₂ i
        LE-TreeItem-t₁₂-i = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node t₁₂ i nilTree)
        OT =
          begin
            ordTree (node t₁₂ i nilTree )
              ≡⟨ ordTree-node t₁₂ i nilTree ⟩
            ordTree t₁₂ &&
            ordTree nilTree &&
            ≤-TreeItem t₁₂ i &&
            ≤-ItemTree i nilTree
              ≡⟨ subst₄ (λ w x y z → ordTree t₁₂ &&
                                     ordTree nilTree &&
                                     ≤-TreeItem t₁₂ i &&
                                     ≤-ItemTree i nilTree ≡
                                     w && x && y && z)
                        OrdTree-t₁₂
                        ordTree-nilTree
                        LE-TreeItem-t₁₂-i
                        LE-ItemTree-i-niltree
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

flatten-OrdList-aux {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                    (tipT {i₂} Ni₂) OTt =
  begin
    ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂))
      ≡⟨ subst (λ x → ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂)) ≡
                      ≤-Lists x                           (flatten (tip i₂)))
               (flatten-node t₁₁ i₁ t₁₂ )
               refl
      ⟩
    ≤-Lists (flatten t₁₁ ++  flatten t₁₂) (flatten (tip i₂))
      ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-ListN Tt₁₁)
                               (flatten-ListN Tt₁₂)
                               (flatten-ListN (tipT Ni₂))
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
    aux₂ = ordTree-Bool (tipT Ni₂)
    aux₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
    aux₄ = ≤-ItemTree-Bool Ni (tipT Ni₂)
    aux₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (tip i₂))) OTt

    -- Auxiliary terms to get the conjuncts from the third conjunct of OTt.
    aux₆ = ≤-TreeItem-Bool Tt₁₁ Ni
    aux₇ = ≤-TreeItem-Bool Tt₁₂ Ni
    aux₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                 (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i₂ : OrdTree (tip i₂)
    OrdTree-tip-i₂ = &&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-ItemTree-i-tip-i₂ : LE-ItemTree i (tip i₂)
    LE-ItemTree-i-tip-i₂ = &&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten t₁₁) (flatten (tip i₂))
    lemma₁ = flatten-OrdList-aux Tt₁₁ Ni (tipT Ni₂) OT  -- IH.
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t₁₁-i : LE-TreeItem t₁₁ i
        LE-TreeItem-t₁₁-i = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node t₁₁ i (tip i₂))
        OT =
          begin
            ordTree (node t₁₁ i (tip i₂) )
              ≡⟨ ordTree-node t₁₁ i (tip i₂) ⟩
            ordTree t₁₁ &&
            ordTree (tip i₂) &&
            ≤-TreeItem t₁₁ i &&
            ≤-ItemTree i (tip i₂)
              ≡⟨ subst₄ (λ w x y z → ordTree t₁₁ &&
                                     ordTree (tip i₂) &&
                                     ≤-TreeItem t₁₁ i &&
                                     ≤-ItemTree i (tip i₂) ≡
                                     w && x && y && z)
                        OrdTree-t₁₁
                        OrdTree-tip-i₂
                        LE-TreeItem-t₁₁-i
                        LE-ItemTree-i-tip-i₂
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten t₁₂) (flatten (tip i₂))
    lemma₂ = flatten-OrdList-aux Tt₁₂ Ni (tipT Ni₂) OT  -- IH.
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t₁₂-i : LE-TreeItem t₁₂ i
        LE-TreeItem-t₁₂-i = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node t₁₂ i (tip i₂))
        OT =
          begin
            ordTree (node t₁₂ i (tip i₂) )
              ≡⟨ ordTree-node t₁₂ i (tip i₂) ⟩
            ordTree t₁₂ &&
            ordTree (tip i₂) &&
            ≤-TreeItem t₁₂ i &&
            ≤-ItemTree i (tip i₂)
              ≡⟨ subst₄ (λ w x y z → ordTree t₁₂ &&
                                     ordTree (tip i₂) &&
                                     ≤-TreeItem t₁₂ i &&
                                     ≤-ItemTree i (tip i₂) ≡
                                     w && x && y && z)
                        OrdTree-t₁₂
                        OrdTree-tip-i₂
                        LE-TreeItem-t₁₂-i
                        LE-ItemTree-i-tip-i₂
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

flatten-OrdList-aux {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                    (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt =
  begin
    ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (node t₂₁ i₂ t₂₂))
      ≡⟨ subst (λ x → ≤-Lists (flatten (node t₁₁ i₁ t₁₂))
                              (flatten (node t₂₁ i₂ t₂₂)) ≡
                      ≤-Lists x (flatten (node t₂₁ i₂ t₂₂)))
               (flatten-node t₁₁ i₁ t₁₂ )
               refl
      ⟩
    ≤-Lists (flatten t₁₁ ++  flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
      ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-ListN Tt₁₁)
                               (flatten-ListN Tt₁₂)
                               (flatten-ListN (nodeT Tt₂₁ Ni₂ Tt₂₂))
                               lemma₁
                               lemma₂
      ⟩
    true
  ∎
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
    aux₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
    aux₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
    aux₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
    aux₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (node t₂₁ i₂ t₂₂))) OTt

    -- Auxiliary terms to get the conjuncts from the third conjunct of OTt.
    aux₆ = ≤-TreeItem-Bool Tt₁₁ Ni
    aux₇ = ≤-TreeItem-Bool Tt₁₂ Ni
    aux₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                 (&&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-node-t₂₁-i₂-t₂₂ : OrdTree (node t₂₁ i₂ t₂₂)
    OrdTree-node-t₂₁-i₂-t₂₂ = &&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-ItemTree-i-node-t₂₁-i₂-t₂₂ : LE-ItemTree i (node t₂₁ i₂ t₂₂)
    LE-ItemTree-i-node-t₂₁-i₂-t₂₂ = &&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten t₁₁) (flatten (node t₂₁ i₂ t₂₂))
    lemma₁ = flatten-OrdList-aux Tt₁₁ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT  -- IH.
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t₁₁-i : LE-TreeItem t₁₁ i
        LE-TreeItem-t₁₁-i = &&-proj₁ aux₆ aux₇ aux₈

        OT : OrdTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
        OT =
          begin
            ordTree (node t₁₁ i (node t₂₁ i₂ t₂₂) )
              ≡⟨ ordTree-node t₁₁ i (node t₂₁ i₂ t₂₂) ⟩
            ordTree t₁₁ &&
            ordTree (node t₂₁ i₂ t₂₂) &&
            ≤-TreeItem t₁₁ i &&
            ≤-ItemTree i (node t₂₁ i₂ t₂₂)
              ≡⟨ subst₄ (λ w x y z → ordTree t₁₁ &&
                                     ordTree (node t₂₁ i₂ t₂₂) &&
                                     ≤-TreeItem t₁₁ i &&
                                     ≤-ItemTree i (node t₂₁ i₂ t₂₂) ≡
                                     w && x && y && z)
                        OrdTree-t₁₁
                        OrdTree-node-t₂₁-i₂-t₂₂
                        LE-TreeItem-t₁₁-i
                        LE-ItemTree-i-node-t₂₁-i₂-t₂₂
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎

    lemma₂ : LE-Lists (flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
    lemma₂ = flatten-OrdList-aux Tt₁₂ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT  -- IH.
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-TreeItem-t₁₂-i : LE-TreeItem t₁₂ i
        LE-TreeItem-t₁₂-i = &&-proj₂ aux₆ aux₇ aux₈

        OT : OrdTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
        OT =
          begin
            ordTree (node t₁₂ i (node t₂₁ i₂ t₂₂) )
              ≡⟨ ordTree-node t₁₂ i (node t₂₁ i₂ t₂₂) ⟩
            ordTree t₁₂ &&
            ordTree (node t₂₁ i₂ t₂₂) &&
            ≤-TreeItem t₁₂ i &&
            ≤-ItemTree i (node t₂₁ i₂ t₂₂)
              ≡⟨ subst₄ (λ w x y z → ordTree t₁₂ &&
                                     ordTree (node t₂₁ i₂ t₂₂) &&
                                     ≤-TreeItem t₁₂ i &&
                                     ≤-ItemTree i (node t₂₁ i₂ t₂₂) ≡
                                     w && x && y && z)
                        OrdTree-t₁₂
                        OrdTree-node-t₂₁-i₂-t₂₂
                        LE-TreeItem-t₁₂-i
                        LE-ItemTree-i-node-t₂₁-i₂-t₂₂
                        refl
            ⟩
            true && true && true && true
              ≡⟨ &&-true₄ ⟩
            true
          ∎
