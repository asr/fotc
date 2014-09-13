------------------------------------------------------------------------------
-- Totality properties respect to OrdList (flatten-OrdList-helper)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- The termination checker can not determine that the function
-- flatten-OrdList-helper is defined by structural recursion because
-- we are using postulates.

module FOT.FOTC.Program.SortList.Properties.Totality.OrdList.FlattenI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
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
                         ≤-Lists (flatten t₁) (flatten t₂)

flatten-OrdList-helper {t₂ = t₂} tnil Ni Tt₂ OTt =
  subst (λ t → ≤-Lists t (flatten t₂))
        (sym (flatten-nil))
        (le-Lists-[] (flatten t₂))

flatten-OrdList-helper (ttip {i₁} Ni₁) _ tnil OTt =
  le-Lists (flatten (tip i₁)) (flatten nil)
    ≡⟨ subst₂ (λ x₁ x₂ → le-Lists (flatten (tip i₁)) (flatten nil) ≡
                         le-Lists x₁ x₂)
              (flatten-tip i₁)
              flatten-nil
              refl
    ⟩
  le-Lists (i₁ ∷ []) []
    ≡⟨ le-Lists-∷ i₁ [] [] ⟩
  le-ItemList i₁ [] && le-Lists [] []
    ≡⟨ subst₂ (λ x₁ x₂ → le-ItemList i₁ [] && le-Lists [] [] ≡ x₁ && x₂)
              (le-ItemList-[] i₁)
              (le-Lists-[] [])
              refl
    ⟩
  true && true
    ≡⟨ t&&x≡x true ⟩
  true ∎

flatten-OrdList-helper {i = i} (ttip {i₁} Ni₁) Ni (ttip {i₂} Ni₂) OTt =
  le-Lists (flatten (tip i₁)) (flatten (tip i₂))
    ≡⟨ subst₂ (λ x₁ x₂ → le-Lists (flatten (tip i₁)) (flatten (tip i₂)) ≡
                         le-Lists x₁ x₂)
              (flatten-tip i₁)
              (flatten-tip i₂)
              refl
    ⟩
  le-Lists (i₁ ∷ []) (i₂ ∷ [])
    ≡⟨ le-Lists-∷ i₁ [] (i₂ ∷ []) ⟩
  le-ItemList i₁ (i₂ ∷ []) && le-Lists [] (i₂ ∷ [])
    ≡⟨ subst (λ t → le-ItemList i₁ (i₂ ∷ []) && le-Lists [] (i₂ ∷ []) ≡
                    t && le-Lists [] (i₂ ∷ []))
             (le-ItemList-∷ i₁ i₂ [])
             refl
    ⟩
  (le i₁ i₂ && le-ItemList i₁ []) && le-Lists [] (i₂ ∷ [])
    ≡⟨ subst (λ t → (le i₁ i₂ && le-ItemList i₁ []) && le-Lists [] (i₂ ∷ []) ≡
                    (t        && le-ItemList i₁ []) && le-Lists [] (i₂ ∷ []))
             lemma
             refl
    ⟩
  (true && le-ItemList i₁ []) && le-Lists [] (i₂ ∷ [])
    ≡⟨ subst₂ (λ x₁ x₂ → (true && le-ItemList i₁ []) && le-Lists [] (i₂ ∷ []) ≡
                         (true && x₁)               && x₂)
              (le-ItemList-[] i₁)
              (le-Lists-[] (i₂ ∷ []))
              refl
    ⟩
  (true && true) && true
    ≡⟨ &&-assoc btrue btrue btrue ⟩
  true && true && true
    ≡⟨ &&-list₃-all-t btrue btrue btrue (refl , refl , refl) ⟩
  true
  ∎
  where
    helper₁ : Bool (ordTree (tip i₁))
    helper₁ = ordTree-Bool (ttip Ni₁)

    helper₂ : Bool (ordTree (tip i₂))
    helper₂ = ordTree-Bool (ttip Ni₂)

    helper₃ : Bool (le-TreeItem (tip i₁) i)
    helper₃ = le-TreeItem-Bool (ttip Ni₁) Ni

    helper₄ : Bool (le-ItemTree i (tip i₂))
    helper₄ = le-ItemTree-Bool Ni (ttip Ni₂)

    helper₅ : ordTree (tip i₁) &&
              ordTree (tip i₂) &&
              le-TreeItem (tip i₁) i &&
              le-ItemTree i (tip i₂) ≡ true
    helper₅ = trans (sym (ordTree-node (tip i₁) i (tip i₂))) OTt

    lemma : i₁ ≤ i₂
    lemma = ≤-trans Ni₁ Ni Ni₂ i₁≤i i≤i₂
     where
       i₁≤i : i₁ ≤ i
       i₁≤i = trans (sym (le-TreeItem-tip i₁ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

       i≤i₂ : i ≤ i₂
       i≤i₂ = trans (sym (le-ItemTree-tip i i₂))
                    (&&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅)

flatten-OrdList-helper {i = i} (ttip {i₁} Ni₁) Ni
                       (tnode {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt =
  le-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂))
    ≡⟨ subst (λ x → le-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂)) ≡
                    le-Lists (flatten (tip i₁)) x)
             (flatten-node t₂₁ i₂ t₂₂)
             refl
    ⟩
  le-Lists (flatten (tip i₁)) (flatten t₂₁ ++ flatten t₂₂)
    ≡⟨ xs≤ys→xs≤zs→xs≤ys++zs (flatten-ListN (ttip Ni₁))
                             (flatten-ListN Tt₂₁)
                             (flatten-ListN Tt₂₂)
                             lemma₁
                             lemma₂
    ⟩
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (ttip Ni₁)
    helper₂ = ordTree-Bool (tnode Tt₂₁ Ni₂ Tt₂₂)
    helper₃ = le-TreeItem-Bool (ttip Ni₁) Ni
    helper₄ = le-ItemTree-Bool Ni (tnode Tt₂₁ Ni₂ Tt₂₂)
    helper₅ = trans (sym (ordTree-node (tip i₁) i (node t₂₁ i₂ t₂₂))) OTt

    -- Helper terms to get the conjuncts from the fourth conjunct of OTt.
    helper₆ = le-ItemTree-Bool Ni Tt₂₁
    helper₇ = le-ItemTree-Bool Ni Tt₂₂
    helper₈ = trans (sym (le-ItemTree-node i t₂₁ i₂ t₂₂))
                    (&&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i₁ : OrdTree (tip i₁)
    OrdTree-tip-i₁ = &&-list₄-t₁ helper₁ helper₂ helper₃ helper₄ helper₅

    ≤-TreeItem-tip-i₁-i : ≤-TreeItem (tip i₁) i
    ≤-TreeItem-tip-i₁-i = &&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅

    lemma₁ : ≤-Lists (flatten (tip i₁)) (flatten t₂₁)
    lemma₁ = flatten-OrdList-helper (ttip Ni₁) Ni Tt₂₁ OT
      where
        OrdTree-t₂₁ : OrdTree t₂₁
        OrdTree-t₂₁ =
          leftSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂ (&&-list₄-t₂ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        ≤-ItemTree-i-t₂₁ : ≤-ItemTree i t₂₁
        ≤-ItemTree-i-t₂₁ = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node (tip i₁) i t₂₁)
        OT = ordTree (node (tip i₁) i t₂₁)
               ≡⟨ ordTree-node (tip i₁) i t₂₁ ⟩
             ordTree (tip i₁) &&
             ordTree t₂₁ &&
             le-TreeItem (tip i₁) i &&
             le-ItemTree i t₂₁
               ≡⟨ subst₄ (λ w x y z → ordTree (tip i₁) &&
                                      ordTree t₂₁ &&
                                      le-TreeItem (tip i₁) i &&
                                      le-ItemTree i t₂₁ ≡
                                      w && x && y && z)
                         OrdTree-tip-i₁
                         OrdTree-t₂₁
                         ≤-TreeItem-tip-i₁-i
                         ≤-ItemTree-i-t₂₁
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : ≤-Lists (flatten (tip i₁)) (flatten t₂₂)
    lemma₂ = flatten-OrdList-helper (ttip Ni₁) Ni Tt₂₂ OT
      where
        OrdTree-t₂₂ : OrdTree t₂₂
        OrdTree-t₂₂ =
          rightSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂ (&&-list₄-t₂ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        ≤-ItemTree-i-t₂₂ : ≤-ItemTree i t₂₂
        ≤-ItemTree-i-t₂₂ = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node (tip i₁) i t₂₂)
        OT = ordTree (node (tip i₁) i t₂₂)
               ≡⟨ ordTree-node (tip i₁) i t₂₂ ⟩
             ordTree (tip i₁) &&
             ordTree t₂₂ &&
             le-TreeItem (tip i₁) i &&
             le-ItemTree i t₂₂
               ≡⟨ subst₄ (λ w x y z → ordTree (tip i₁) &&
                                      ordTree t₂₂ &&
                                      le-TreeItem (tip i₁) i &&
                                      le-ItemTree i t₂₂ ≡
                                      w && x && y && z)
                         OrdTree-tip-i₁
                         OrdTree-t₂₂
                         ≤-TreeItem-tip-i₁-i
                         ≤-ItemTree-i-t₂₂
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

flatten-OrdList-helper {i = i} (tnode {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni tnil OTt =
  le-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nil)
    ≡⟨ subst (λ x → le-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nil) ≡
                    le-Lists x                           (flatten nil))
             (flatten-node t₁₁ i₁ t₁₂)
             refl
    ⟩
  le-Lists (flatten t₁₁ ++  flatten t₁₂) (flatten nil)
    ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-ListN Tt₁₁)
                             (flatten-ListN Tt₁₂)
                             (flatten-ListN tnil)
                             lemma₁
                             lemma₂
    ⟩
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (tnode Tt₁₁ Ni₁ Tt₁₂)
    helper₂ = ordTree-Bool tnil
    helper₃ = le-TreeItem-Bool (tnode Tt₁₁ Ni₁ Tt₁₂) Ni
    helper₄ = le-ItemTree-Bool Ni tnil
    helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i nil)) OTt

    -- Helper terms to get the conjuncts from the third conjunct of OTt.
    helper₆ = le-TreeItem-Bool Tt₁₁ Ni
    helper₇ = le-TreeItem-Bool Tt₁₂ Ni
    helper₈ = trans (sym (le-TreeItem-node t₁₁ i₁ t₁₂ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    ≤-ItemTree-i-niltree : ≤-ItemTree i nil
    ≤-ItemTree-i-niltree = &&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅

    lemma₁ : ≤-Lists (flatten t₁₁) (flatten nil)
    lemma₁ = flatten-OrdList-helper Tt₁₁ Ni tnil OT
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        ≤-TreeItem-t₁₁-i : ≤-TreeItem t₁₁ i
        ≤-TreeItem-t₁₁-i = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₁ i nil)
        OT = ordTree (node t₁₁ i nil)
               ≡⟨ ordTree-node t₁₁ i nil ⟩
             ordTree t₁₁ &&
             ordTree nil &&
             le-TreeItem t₁₁ i &&
             le-ItemTree i nil
               ≡⟨ subst₄ (λ w x y z → ordTree t₁₁ &&
                                      ordTree nil &&
                                      le-TreeItem t₁₁ i &&
                                      le-ItemTree i nil ≡
                                      w && x && y && z)
                         OrdTree-t₁₁
                         ordTree-nil
                         ≤-TreeItem-t₁₁-i
                         ≤-ItemTree-i-niltree
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : ≤-Lists (flatten t₁₂) (flatten nil)
    lemma₂ = flatten-OrdList-helper Tt₁₂ Ni tnil OT
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        ≤-TreeItem-t₁₂-i : ≤-TreeItem t₁₂ i
        ≤-TreeItem-t₁₂-i = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₂ i nil)
        OT = ordTree (node t₁₂ i nil)
              ≡⟨ ordTree-node t₁₂ i nil ⟩
             ordTree t₁₂ &&
             ordTree nil &&
             le-TreeItem t₁₂ i &&
             le-ItemTree i nil
               ≡⟨ subst₄ (λ w x y z → ordTree t₁₂ &&
                                      ordTree nil &&
                                      le-TreeItem t₁₂ i &&
                                      le-ItemTree i nil ≡
                                      w && x && y && z)
                         OrdTree-t₁₂
                         ordTree-nil
                         ≤-TreeItem-t₁₂-i
                         ≤-ItemTree-i-niltree
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

flatten-OrdList-helper {i = i} (tnode {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (ttip {i₂} Ni₂) OTt =
  le-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂))
    ≡⟨ subst (λ x → le-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂)) ≡
                    le-Lists x                           (flatten (tip i₂)))
             (flatten-node t₁₁ i₁ t₁₂)
             refl
    ⟩
  le-Lists (flatten t₁₁ ++  flatten t₁₂) (flatten (tip i₂))
    ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-ListN Tt₁₁)
                             (flatten-ListN Tt₁₂)
                             (flatten-ListN (ttip Ni₂))
                             lemma₁
                             lemma₂
    ⟩
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (tnode Tt₁₁ Ni₁ Tt₁₂)
    helper₂ = ordTree-Bool (ttip Ni₂)
    helper₃ = le-TreeItem-Bool (tnode Tt₁₁ Ni₁ Tt₁₂) Ni
    helper₄ = le-ItemTree-Bool Ni (ttip Ni₂)
    helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (tip i₂))) OTt

    -- Helper terms to get the conjuncts from the third conjunct of OTt.
    helper₆ = le-TreeItem-Bool Tt₁₁ Ni
    helper₇ = le-TreeItem-Bool Tt₁₂ Ni
    helper₈ = trans (sym (le-TreeItem-node t₁₁ i₁ t₁₂ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-tip-i₂ : OrdTree (tip i₂)
    OrdTree-tip-i₂ = &&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅

    ≤-ItemTree-i-tip-i₂ : ≤-ItemTree i (tip i₂)
    ≤-ItemTree-i-tip-i₂ = &&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅

    lemma₁ : ≤-Lists (flatten t₁₁) (flatten (tip i₂))
    lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (ttip Ni₂) OT
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        ≤-TreeItem-t₁₁-i : ≤-TreeItem t₁₁ i
        ≤-TreeItem-t₁₁-i = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₁ i (tip i₂))
        OT = ordTree (node t₁₁ i (tip i₂))
               ≡⟨ ordTree-node t₁₁ i (tip i₂) ⟩
             ordTree t₁₁ &&
             ordTree (tip i₂) &&
             le-TreeItem t₁₁ i &&
             le-ItemTree i (tip i₂)
               ≡⟨ subst₄ (λ w x y z → ordTree t₁₁ &&
                                      ordTree (tip i₂) &&
                                      le-TreeItem t₁₁ i &&
                                      le-ItemTree i (tip i₂) ≡
                                      w && x && y && z)
                         OrdTree-t₁₁
                         OrdTree-tip-i₂
                         ≤-TreeItem-t₁₁-i
                         ≤-ItemTree-i-tip-i₂
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : ≤-Lists (flatten t₁₂) (flatten (tip i₂))
    lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (ttip Ni₂) OT
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        ≤-TreeItem-t₁₂-i : ≤-TreeItem t₁₂ i
        ≤-TreeItem-t₁₂-i = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₂ i (tip i₂))
        OT = ordTree (node t₁₂ i (tip i₂))
               ≡⟨ ordTree-node t₁₂ i (tip i₂) ⟩
             ordTree t₁₂ &&
             ordTree (tip i₂) &&
             le-TreeItem t₁₂ i &&
             le-ItemTree i (tip i₂)
               ≡⟨ subst₄ (λ w x y z → ordTree t₁₂ &&
                                      ordTree (tip i₂) &&
                                      le-TreeItem t₁₂ i &&
                                      le-ItemTree i (tip i₂) ≡
                                      w && x && y && z)
                         OrdTree-t₁₂
                         OrdTree-tip-i₂
                         ≤-TreeItem-t₁₂-i
                         ≤-ItemTree-i-tip-i₂
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

flatten-OrdList-helper {i = i} (tnode {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (tnode {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt =
  le-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (node t₂₁ i₂ t₂₂))
    ≡⟨ subst (λ x → le-Lists (flatten (node t₁₁ i₁ t₁₂))
                            (flatten (node t₂₁ i₂ t₂₂)) ≡
                    le-Lists x (flatten (node t₂₁ i₂ t₂₂)))
             (flatten-node t₁₁ i₁ t₁₂)
             refl
    ⟩
  le-Lists (flatten t₁₁ ++  flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
    ≡⟨ xs≤zs→ys≤zs→xs++ys≤zs (flatten-ListN Tt₁₁)
                             (flatten-ListN Tt₁₂)
                             (flatten-ListN (tnode Tt₂₁ Ni₂ Tt₂₂))
                             lemma₁
                             lemma₂
    ⟩
  true ∎
  where
    -- Helper terms to get the conjuncts from OTt.
    helper₁ = ordTree-Bool (tnode Tt₁₁ Ni₁ Tt₁₂)
    helper₂ = ordTree-Bool (tnode Tt₂₁ Ni₂ Tt₂₂)
    helper₃ = le-TreeItem-Bool (tnode Tt₁₁ Ni₁ Tt₁₂) Ni
    helper₄ = le-ItemTree-Bool Ni (tnode Tt₂₁ Ni₂ Tt₂₂)
    helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (node t₂₁ i₂ t₂₂))) OTt

    -- Helper terms to get the conjuncts from the third conjunct of OTt.
    helper₆ = le-TreeItem-Bool Tt₁₁ Ni
    helper₇ = le-TreeItem-Bool Tt₁₂ Ni
    helper₈ = trans (sym (le-TreeItem-node t₁₁ i₁ t₁₂ i))
                    (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

    -- Common terms for the lemma₁ and lemma₂.
    OrdTree-node-t₂₁-i₂-t₂₂ : OrdTree (node t₂₁ i₂ t₂₂)
    OrdTree-node-t₂₁-i₂-t₂₂ = &&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅

    ≤-ItemTree-i-node-t₂₁-i₂-t₂₂ : ≤-ItemTree i (node t₂₁ i₂ t₂₂)
    ≤-ItemTree-i-node-t₂₁-i₂-t₂₂ = &&-list₄-t₄ helper₁ helper₂ helper₃ helper₄
                                                helper₅

    lemma₁ : ≤-Lists (flatten t₁₁) (flatten (node t₂₁ i₂ t₂₂))
    lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (tnode Tt₂₁ Ni₂ Tt₂₂) OT
      where
        OrdTree-t₁₁ : OrdTree t₁₁
        OrdTree-t₁₁ =
          leftSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                         helper₄ helper₅)

        ≤-TreeItem-t₁₁-i : ≤-TreeItem t₁₁ i
        ≤-TreeItem-t₁₁-i = &&-list₂-t₁ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
        OT = ordTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
               ≡⟨ ordTree-node t₁₁ i (node t₂₁ i₂ t₂₂) ⟩
             ordTree t₁₁ &&
             ordTree (node t₂₁ i₂ t₂₂) &&
             le-TreeItem t₁₁ i &&
             le-ItemTree i (node t₂₁ i₂ t₂₂)
               ≡⟨ subst₄ (λ w x y z → ordTree t₁₁ &&
                                      ordTree (node t₂₁ i₂ t₂₂) &&
                                      le-TreeItem t₁₁ i &&
                                      le-ItemTree i (node t₂₁ i₂ t₂₂) ≡
                                      w && x && y && z)
                         OrdTree-t₁₁
                         OrdTree-node-t₂₁-i₂-t₂₂
                         ≤-TreeItem-t₁₁-i
                         ≤-ItemTree-i-node-t₂₁-i₂-t₂₂
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true ∎

    lemma₂ : ≤-Lists (flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
    lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (tnode Tt₂₁ Ni₂ Tt₂₂) OT
      where
        OrdTree-t₁₂ : OrdTree t₁₂
        OrdTree-t₁₂ =
          rightSubTree-OrdTree Tt₁₁ Ni₁ Tt₁₂ (&&-list₄-t₁ helper₁ helper₂ helper₃
                                                          helper₄ helper₅)

        ≤-TreeItem-t₁₂-i : ≤-TreeItem t₁₂ i
        ≤-TreeItem-t₁₂-i = &&-list₂-t₂ helper₆ helper₇ helper₈

        OT : OrdTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
        OT = ordTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
               ≡⟨ ordTree-node t₁₂ i (node t₂₁ i₂ t₂₂) ⟩
             ordTree t₁₂ &&
             ordTree (node t₂₁ i₂ t₂₂) &&
             le-TreeItem t₁₂ i &&
             le-ItemTree i (node t₂₁ i₂ t₂₂)
               ≡⟨ subst₄ (λ w x y z → ordTree t₁₂ &&
                                      ordTree (node t₂₁ i₂ t₂₂) &&
                                      le-TreeItem t₁₂ i &&
                                      le-ItemTree i (node t₂₁ i₂ t₂₂) ≡
                                      w && x && y && z)
                         OrdTree-t₁₂
                         OrdTree-node-t₂₁-i₂-t₂₂
                         ≤-TreeItem-t₁₂-i
                         ≤-ItemTree-i-node-t₂₁-i₂-t₂₂
                         refl
             ⟩
             true && true && true && true
               ≡⟨ &&-list₄-all-t btrue btrue btrue btrue (refl , refl , refl , refl) ⟩
             true
           ∎
