------------------------------------------------------------------------------
-- Totality properties respect to OrdList (flatten-OrdList-helper)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The termination checker can not determine that the function
-- flatten-OrdList-helper is defined by structural recursion because
-- we are using postulates.

module FOT.FOTC.Program.SortList.Properties.Totality.OrdList.FlattenI where

open import FOTC.Base

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Data.List

open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.Properties.Totality.ListN-I
open import FOTC.Program.SortList.Properties.Totality.OrdTreeI
open import FOTC.Program.SortList.Properties.MiscellaneousI
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
flatten-OrdList-helper : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                         OrdTree (node t₁ i t₂) →
                         LE-Lists (flatten t₁) (flatten t₂)

flatten-OrdList-helper {t₂ = t₂} nilT Ni Tt₂ OTt =
  subst (λ t → LE-Lists t (flatten t₂))
        (sym (flatten-nilTree))
        (≤-Lists-[] (flatten t₂))

flatten-OrdList-helper (tipT {i₁} Ni₁) _ nilT OTt =
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
    ≡⟨ t&&x≡x true ⟩
  true ∎

flatten-OrdList-helper {i = i} (tipT {i₁} Ni₁) Ni (tipT {i₂} Ni₂) OTt =
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
  ((i₁ ≤ i₂) && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ [])
    ≡⟨ subst (λ t → ((i₁ ≤ i₂)  && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ []) ≡
                    (t          && ≤-ItemList i₁ []) && ≤-Lists [] (i₂ ∷ []))
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
    ≡⟨ &&-list₃-all-t tB tB tB (refl , refl , refl) ⟩
  true
  ∎
  where
    helper₁ : Bool (ordTree (tip i₁))
    helper₁ = ordTree-Bool (tipT Ni₁)

    helper₂ : Bool (ordTree (tip i₂))
    helper₂ = ordTree-Bool (tipT Ni₂)

    helper₃ : Bool (≤-TreeItem (tip i₁) i)
    helper₃ = ≤-TreeItem-Bool (tipT Ni₁) Ni

    helper₄ : Bool (≤-ItemTree i (tip i₂))
    helper₄ = ≤-ItemTree-Bool Ni (tipT Ni₂)

    helper₅ : ordTree (tip i₁) &&
           ordTree (tip i₂) &&
           ≤-TreeItem (tip i₁) i &&
           ≤-ItemTree i (tip i₂) ≡ true
    helper₅ = trans (sym (ordTree-node (tip i₁) i (tip i₂))) OTt

    lemma : LE i₁ i₂
    lemma = ≤-trans Ni₁ Ni Ni₂ i₁≤i i≤i₂
     where
       i₁≤i : LE i₁ i
       i₁≤i = trans (sym (≤-TreeItem-tip i₁ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

       i≤i₂ : LE i i₂
       i≤i₂ = trans (sym (≤-ItemTree-tip i i₂))
                    (&&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅)

flatten-OrdList-helper {i = i} (tipT {i₁} Ni₁) Ni
                       (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt =
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
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (tipT Ni₁)
    helper₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
    helper₃ = ≤-TreeItem-Bool (tipT Ni₁) Ni
    helper₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
    helper₅ = trans (sym (ordTree-node (tip i₁) i (node t₂₁ i₂ t₂₂))) OTt

    -- Helper terms to get the conjuncts from the fourth conjunct of OTt.
    helper₆ = ≤-ItemTree-Bool Ni Tt₂₁
    helper₇ = ≤-ItemTree-Bool Ni Tt₂₂
    helper₈ = trans (sym (≤-ItemTree-node i t₂₁ i₂ t₂₂))
                    (&&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i₁ : OrdTree (tip i₁)
    OrdTree-tip-i₁ = &&-list₄-t₁ helper₁ helper₂ helper₃ helper₄ helper₅

    LE-TreeItem-tip-i₁-i : LE-TreeItem (tip i₁) i
    LE-TreeItem-tip-i₁-i = &&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅

    lemma₁ : LE-Lists (flatten (tip i₁)) (flatten t₂₁)
    lemma₁ = flatten-OrdList-helper (tipT Ni₁) Ni Tt₂₁ OT
      where
        OrdTree-t₂₁ : OrdTree t₂₁
        OrdTree-t₂₁ =
          leftSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂ (&&-list₄-t₂ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        LE-ItemTree-i-t₂₁ : LE-ItemTree i t₂₁
        LE-ItemTree-i-t₂₁ = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node (tip i₁) i t₂₁)
        OT = ordTree (node (tip i₁) i t₂₁)
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : LE-Lists (flatten (tip i₁)) (flatten t₂₂)
    lemma₂ = flatten-OrdList-helper (tipT Ni₁) Ni Tt₂₂ OT
      where
        OrdTree-t₂₂ : OrdTree t₂₂
        OrdTree-t₂₂ =
          rightSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂ (&&-list₄-t₂ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        LE-ItemTree-i-t₂₂ : LE-ItemTree i t₂₂
        LE-ItemTree-i-t₂₂ = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node (tip i₁) i t₂₂)
        OT = ordTree (node (tip i₁) i t₂₂)
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

flatten-OrdList-helper {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni nilT OTt =
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
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
    helper₂ = ordTree-Bool nilT
    helper₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
    helper₄ = ≤-ItemTree-Bool Ni nilT
    helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i nilTree )) OTt

    -- Helper terms to get the conjuncts from the third conjunct of OTt.
    helper₆ = ≤-TreeItem-Bool Tt₁₁ Ni
    helper₇ = ≤-TreeItem-Bool Tt₁₂ Ni
    helper₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    LE-ItemTree-i-niltree : LE-ItemTree i nilTree
    LE-ItemTree-i-niltree = &&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅

    lemma₁ : LE-Lists (flatten t₁₁) (flatten nilTree)
    lemma₁ = flatten-OrdList-helper Tt₁₁ Ni nilT OT
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        LE-TreeItem-t₁₁-i : LE-TreeItem t₁₁ i
        LE-TreeItem-t₁₁-i = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₁ i nilTree)
        OT = ordTree (node t₁₁ i nilTree )
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : LE-Lists (flatten t₁₂) (flatten nilTree)
    lemma₂ = flatten-OrdList-helper Tt₁₂ Ni nilT OT
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        LE-TreeItem-t₁₂-i : LE-TreeItem t₁₂ i
        LE-TreeItem-t₁₂-i = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₂ i nilTree)
        OT = ordTree (node t₁₂ i nilTree )
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

flatten-OrdList-helper {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (tipT {i₂} Ni₂) OTt =
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
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
    helper₂ = ordTree-Bool (tipT Ni₂)
    helper₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
    helper₄ = ≤-ItemTree-Bool Ni (tipT Ni₂)
    helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (tip i₂))) OTt

    -- Helper terms to get the conjuncts from the third conjunct of OTt.
    helper₆ = ≤-TreeItem-Bool Tt₁₁ Ni
    helper₇ = ≤-TreeItem-Bool Tt₁₂ Ni
    helper₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i₂ : OrdTree (tip i₂)
    OrdTree-tip-i₂ = &&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅

    LE-ItemTree-i-tip-i₂ : LE-ItemTree i (tip i₂)
    LE-ItemTree-i-tip-i₂ = &&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅

    lemma₁ : LE-Lists (flatten t₁₁) (flatten (tip i₂))
    lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (tipT Ni₂) OT
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        LE-TreeItem-t₁₁-i : LE-TreeItem t₁₁ i
        LE-TreeItem-t₁₁-i = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₁ i (tip i₂))
        OT = ordTree (node t₁₁ i (tip i₂) )
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : LE-Lists (flatten t₁₂) (flatten (tip i₂))
    lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (tipT Ni₂) OT
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        LE-TreeItem-t₁₂-i : LE-TreeItem t₁₂ i
        LE-TreeItem-t₁₂-i = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₂ i (tip i₂))
        OT = ordTree (node t₁₂ i (tip i₂) )
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

flatten-OrdList-helper {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt =
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
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
    helper₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
    helper₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
    helper₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
    helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (node t₂₁ i₂ t₂₂))) OTt

    -- Helper terms to get the conjuncts from the third conjunct of OTt.
    helper₆ = ≤-TreeItem-Bool Tt₁₁ Ni
    helper₇ = ≤-TreeItem-Bool Tt₁₂ Ni
    helper₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-node-t₂₁-i₂-t₂₂ : OrdTree (node t₂₁ i₂ t₂₂)
    OrdTree-node-t₂₁-i₂-t₂₂ = &&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅

    LE-ItemTree-i-node-t₂₁-i₂-t₂₂ : LE-ItemTree i (node t₂₁ i₂ t₂₂)
    LE-ItemTree-i-node-t₂₁-i₂-t₂₂ = &&-list₄-t₄ helper₁ helper₂ helper₃ helper₄
                                                helper₅

    lemma₁ : LE-Lists (flatten t₁₁) (flatten (node t₂₁ i₂ t₂₂))
    lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        LE-TreeItem-t₁₁-i : LE-TreeItem t₁₁ i
        LE-TreeItem-t₁₁-i = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
        OT = ordTree (node t₁₁ i (node t₂₁ i₂ t₂₂) )
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : LE-Lists (flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
    lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        LE-TreeItem-t₁₂-i : LE-TreeItem t₁₂ i
        LE-TreeItem-t₁₂-i = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
        OT = ordTree (node t₁₂ i (node t₂₁ i₂ t₂₂) )
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
               ≡⟨ &&-list₄-all-t tB tB tB tB (refl , refl , refl , refl) ⟩
             true
           ∎