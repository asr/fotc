------------------------------------------------------------------------------
-- Totality properties respect to OrdTree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdTreeI where

open import Common.Function

open import FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList
open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.Properties.Totality.TreeI

------------------------------------------------------------------------------
-- Subtrees

-- If (node t₁ i t₂) is ordered then t₁ is ordered.
leftSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                      OrdTree (node t₁ i t₂) → OrdTree t₁
leftSubTree-OrdTree {t₁} {i} {t₂} Tt₁ Ni Tt₂ TOnode =
  ordTree t₁
    ≡⟨ &&-proj₁ (ordTree-Bool Tt₁)
                (&&-Bool (ordTree-Bool Tt₂)
                         (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                  (≤-ItemTree-Bool Ni Tt₂)))
                (trans (sym $ ordTree-node t₁ i t₂) TOnode)
    ⟩
  true ∎

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
rightSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                       OrdTree (node t₁ i t₂) → OrdTree t₂
rightSubTree-OrdTree {t₁} {i} {t₂} Tt₁ Ni Tt₂ TOnode =
  ordTree t₂
    ≡⟨ &&-proj₁
       (ordTree-Bool Tt₂)
         (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                  (≤-ItemTree-Bool Ni Tt₂))
         (&&-proj₂ (ordTree-Bool Tt₁)
                   (&&-Bool (ordTree-Bool Tt₂)
                            (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                     (≤-ItemTree-Bool Ni Tt₂)))
                   (trans (sym $ ordTree-node t₁ i t₂) TOnode))
    ⟩
  true ∎

------------------------------------------------------------------------------
-- Helper functions

toTree-OrdTree-helper₁ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → GT i₁ i₂ →
                         Tree t →
                         LE-TreeItem t i₁ →
                         LE-TreeItem (toTree · i₂ · t) i₁
toTree-OrdTree-helper₁ {i₁} {i₂} .{nilTree} Ni₁ Ni₂ i₁>i₂ nilT _ =
  ≤-TreeItem (toTree · i₂ · nilTree) i₁
    ≡⟨ subst (λ t → ≤-TreeItem (toTree · i₂ · nilTree) i₁ ≡ ≤-TreeItem t i₁)
             (toTree-nilTree i₂)
             refl
    ⟩
  ≤-TreeItem (tip i₂) i₁
    ≡⟨ ≤-TreeItem-tip i₂ i₁ ⟩
  i₂ ≤ i₁
    ≡⟨ x<y→x≤y Ni₂ Ni₁ i₁>i₂ ⟩
  true ∎

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ (tipT {j} Nj) t≤i₁ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : GT j i₂ → LE-TreeItem (toTree · i₂ · tip j) i₁
  prf₁ j>i₂ =
    ≤-TreeItem (toTree · i₂ · tip j) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (toTree · i₂ · tip j) i₁ ≡
                      ≤-TreeItem t i₁)
               (toTree-tip i₂ j)
               refl
      ⟩
    ≤-TreeItem (if (j ≤ i₂)
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → ≤-TreeItem
                      (if (j ≤ i₂)
                          then (node (tip j) i₂ (tip i₂))
                          else (node (tip i₂) j (tip j))) i₁ ≡
                      ≤-TreeItem (if t
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁)
               (x>y→x≰y Nj Ni₂ j>i₂)
               refl
      ⟩
    ≤-TreeItem (if false
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (if false
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁ ≡
                      ≤-TreeItem t i₁)
               (if-false (node (tip i₂) j (tip j)))
               refl
      ⟩
    ≤-TreeItem (node (tip i₂) j (tip j)) i₁
      ≡⟨ ≤-TreeItem-node (tip i₂) j (tip j) i₁ ⟩
    ≤-TreeItem (tip i₂) i₁ && ≤-TreeItem (tip j) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (tip i₂) i₁ && ≤-TreeItem (tip j) i₁ ≡
                      t && ≤-TreeItem (tip j) i₁)
               (≤-TreeItem-tip i₂ i₁)
               refl
      ⟩
    i₂ ≤ i₁ && ≤-TreeItem (tip j) i₁
       ≡⟨ subst (λ t → i₂ ≤ i₁ && ≤-TreeItem (tip j) i₁ ≡
                       t && ≤-TreeItem (tip j) i₁)
                (x<y→x≤y Ni₂ Ni₁ i₁>i₂)
                refl
       ⟩
    true && ≤-TreeItem (tip j) i₁
      ≡⟨ subst (λ t → true && ≤-TreeItem (tip j) i₁ ≡ true && t)
               (≤-TreeItem-tip j i₁)
               refl
      ⟩
    true && j ≤ i₁
      ≡⟨ subst (λ t → true && j ≤ i₁ ≡ true && t)
               -- j ≤ i₁ because by hypothesis we have (tip j) ≤ i₁.
               (trans (sym $ ≤-TreeItem-tip j i₁) t≤i₁)
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

  prf₂ : LE j i₂ → LE-TreeItem (toTree · i₂ · tip j) i₁
  prf₂ j≤i₂ =
    ≤-TreeItem (toTree · i₂ · tip j) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (toTree · i₂ · tip j) i₁ ≡
                      ≤-TreeItem t i₁)
               (toTree-tip i₂ j)
               refl
      ⟩
    ≤-TreeItem (if (j ≤ i₂)
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → ≤-TreeItem
                      (if (j ≤ i₂)
                          then (node (tip j) i₂ (tip i₂))
                          else (node (tip i₂) j (tip j))) i₁ ≡
                      ≤-TreeItem (if t
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁)
               j≤i₂
               refl
      ⟩
    ≤-TreeItem (if true
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (if true
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁ ≡
                      ≤-TreeItem t i₁)
               (if-true (node (tip j) i₂ (tip i₂)))
               refl
         ⟩
    ≤-TreeItem (node (tip j) i₂ (tip i₂)) i₁
      ≡⟨ ≤-TreeItem-node (tip j) i₂ (tip i₂) i₁ ⟩
    ≤-TreeItem (tip j) i₁ && ≤-TreeItem (tip i₂) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (tip j) i₁ && ≤-TreeItem (tip i₂) i₁ ≡
                      t && ≤-TreeItem (tip i₂) i₁)
               (≤-TreeItem-tip j i₁)
               refl
      ⟩
    j ≤ i₁ && ≤-TreeItem (tip i₂) i₁
      ≡⟨ subst (λ t → j ≤ i₁ && ≤-TreeItem (tip i₂) i₁ ≡
                      t && ≤-TreeItem (tip i₂) i₁)
               -- j ≤ i₁ because by hypothesis we have (tip j) ≤ i₁.
               (trans (sym $ ≤-TreeItem-tip j i₁) t≤i₁)
               refl
      ⟩
    true && ≤-TreeItem (tip i₂) i₁
      ≡⟨ subst (λ t → true && ≤-TreeItem (tip i₂) i₁ ≡ true && t)
               (≤-TreeItem-tip i₂ i₁)
               refl
      ⟩
    true && i₂ ≤ i₁
      ≡⟨ subst (λ t → true && i₂ ≤ i₁ ≡ true && t)
               (x<y→x≤y Ni₂ Ni₁ i₁>i₂)
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                       (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : GT j i₂ → LE-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  prf₁ j>i₂ =
    ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁ ≡
                      ≤-TreeItem t i₁)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    ≤-TreeItem (if (j ≤ i₂)
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → ≤-TreeItem
                        (if (j ≤ i₂)
                            then (node t₁ j (toTree · i₂ · t₂))
                            else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      ≤-TreeItem
                        (if t
                            then (node t₁ j (toTree · i₂ · t₂))
                            else (node (toTree · i₂ · t₁) j t₂)) i₁)
               (x>y→x≰y Nj Ni₂ j>i₂)
               refl
      ⟩
    ≤-TreeItem (if false
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (if false
                                     then (node t₁ j (toTree · i₂ · t₂))
                                     else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      ≤-TreeItem t i₁)
               (if-false (node (toTree · i₂ · t₁) j t₂))
               refl
      ⟩
    ≤-TreeItem (node (toTree · i₂ · t₁) j t₂) i₁
      ≡⟨ ≤-TreeItem-node (toTree · i₂ · t₁) j t₂ i₁ ⟩
    ≤-TreeItem (toTree · i₂ · t₁) i₁ && ≤-TreeItem t₂ i₁
      ≡⟨ subst (λ t → ≤-TreeItem (toTree · i₂ · t₁) i₁ &&
                      ≤-TreeItem t₂ i₁                 ≡
                      t                                &&
                      ≤-TreeItem t₂ i₁)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₁
                 (&&-proj₁ (≤-TreeItem-Bool Tt₁ Ni₁)
                           (≤-TreeItem-Bool Tt₂ Ni₁)
                           (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁)))
               refl
      ⟩
    true && ≤-TreeItem t₂ i₁
      ≡⟨ subst (λ t → true && ≤-TreeItem t₂ i₁ ≡ true && t)
               -- t₂ ≤ i₁ because by hypothesis we have (node t₁ j t₂) ≤ i₁.
               (&&-proj₂ (≤-TreeItem-Bool Tt₁ Ni₁)
                         (≤-TreeItem-Bool Tt₂ Ni₁)
                         (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁))
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

  prf₂ : LE j i₂ → LE-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  prf₂ j≤i₂ =
    ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁ ≡
                      ≤-TreeItem t i₁)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    ≤-TreeItem (if (j ≤ i₂)
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → ≤-TreeItem
                        (if (j ≤ i₂)
                            then (node t₁ j (toTree · i₂ · t₂))
                            else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      ≤-TreeItem
                        (if t
                            then (node t₁ j (toTree · i₂ · t₂))
                            else (node (toTree · i₂ · t₁) j t₂)) i₁)
               (j≤i₂)
               refl
      ⟩
    ≤-TreeItem (if true
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (if true
                                     then (node t₁ j (toTree · i₂ · t₂))
                                     else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      ≤-TreeItem t i₁)
               (if-true (node t₁ j (toTree · i₂ · t₂)))
               refl
      ⟩
    ≤-TreeItem (node t₁ j (toTree · i₂ · t₂)) i₁
      ≡⟨ ≤-TreeItem-node t₁ j (toTree · i₂ · t₂) i₁ ⟩
    ≤-TreeItem t₁ i₁ && ≤-TreeItem (toTree · i₂ · t₂) i₁
      ≡⟨ subst (λ t → ≤-TreeItem t₁ i₁ && ≤-TreeItem (toTree · i₂ · t₂) i₁ ≡
                      t &&  ≤-TreeItem (toTree · i₂ · t₂) i₁)
               -- t₁ ≤ i₁ because by hypothesis we have (node t₁ j t₂) ≤ i₁.
               (&&-proj₁ (≤-TreeItem-Bool Tt₁ Ni₁)
                         (≤-TreeItem-Bool Tt₂ Ni₁)
                         (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁))
               refl
      ⟩
    true && ≤-TreeItem (toTree · i₂ · t₂) i₁
      ≡⟨ subst (λ t → true && ≤-TreeItem (toTree · i₂ · t₂) i₁ ≡
                      true && t)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₂
                 (&&-proj₂ (≤-TreeItem-Bool Tt₁ Ni₁)
                           (≤-TreeItem-Bool Tt₂ Ni₁)
                           (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁)))
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

------------------------------------------------------------------------------

toTree-OrdTree-helper₂ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → LE i₁ i₂ →
                         Tree t →
                         LE-ItemTree i₁ t →
                         LE-ItemTree i₁ (toTree · i₂ · t)
toTree-OrdTree-helper₂ {i₁} {i₂} .{nilTree} _ _ i₁≤i₂ nilT _ =
  ≤-ItemTree i₁ (toTree · i₂ · nilTree)
    ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree · i₂ · nilTree) ≡ ≤-ItemTree i₁ t)
             (toTree-nilTree i₂)
             refl
    ⟩
  ≤-ItemTree i₁ (tip i₂)
    ≡⟨ ≤-ItemTree-tip i₁ i₂ ⟩
  i₁ ≤ i₂
    ≡⟨ i₁≤i₂ ⟩
  true ∎

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (tipT {j} Nj) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree · i₂ · tip j)
  prf₁ j>i₂ =
    ≤-ItemTree i₁ (toTree · i₂ · tip j)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree · i₂ · tip j) ≡
                      ≤-ItemTree i₁ t)
               (toTree-tip i₂ j)
               refl
      ⟩
    ≤-ItemTree i₁ (if (j ≤ i₂)
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (if (j ≤ i₂)
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                      ≤-ItemTree i₁ (if t
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))))
             (x>y→x≰y Nj Ni₂ j>i₂)
             refl
       ⟩
    ≤-ItemTree i₁ (if false
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
    ≡⟨ subst (λ t → ≤-ItemTree i₁ (if false
                                      then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                    ≤-ItemTree i₁ t)
                (if-false (node (tip i₂) j (tip j)))
                refl
       ⟩
    ≤-ItemTree i₁ (node (tip i₂) j (tip j))
      ≡⟨ ≤-ItemTree-node i₁ (tip i₂) j (tip j) ⟩
    ≤-ItemTree i₁ (tip i₂) && ≤-ItemTree i₁ (tip j)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (tip i₂) && ≤-ItemTree i₁ (tip j) ≡
                      t && ≤-ItemTree i₁ (tip j))
               (≤-ItemTree-tip i₁ i₂)
               refl
      ⟩
    i₁ ≤ i₂ && ≤-ItemTree i₁ (tip j)
       ≡⟨ subst (λ t → i₁ ≤ i₂ && ≤-ItemTree i₁ (tip j) ≡
                       t && ≤-ItemTree i₁ (tip j))
                i₁≤i₂
                refl
        ⟩
    true && ≤-ItemTree i₁ (tip j)
      ≡⟨ subst (λ t → true && ≤-ItemTree i₁ (tip j) ≡ true && t)
               (≤-ItemTree-tip i₁ j)
               refl
      ⟩
    true && i₁ ≤ j
      ≡⟨ subst (λ t → true && i₁ ≤ j ≡ true && t)
               -- i₁ ≤ j because by hypothesis we have i₁ ≤ (tip j).
               (trans (sym $ ≤-ItemTree-tip i₁ j) i₁≤t)
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

  prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree · i₂ · tip j)
  prf₂ j≤i₂ =
    ≤-ItemTree i₁ (toTree · i₂ · tip j)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree · i₂ · tip j) ≡
                      ≤-ItemTree i₁ t)
               (toTree-tip i₂ j)
               refl
      ⟩
    ≤-ItemTree i₁ (if (j ≤ i₂)
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (if (j ≤ i₂)
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                      ≤-ItemTree i₁ (if t
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))))
               j≤i₂
               refl
        ⟩
    ≤-ItemTree i₁ (if true
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (if true
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                      ≤-ItemTree i₁ t)
               (if-true (node (tip j) i₂ (tip i₂)))
               refl
      ⟩
    ≤-ItemTree i₁ (node (tip j) i₂ (tip i₂))
      ≡⟨ ≤-ItemTree-node i₁ (tip j) i₂ (tip i₂) ⟩
    ≤-ItemTree i₁ (tip j) && ≤-ItemTree i₁ (tip i₂)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (tip j) && ≤-ItemTree i₁ (tip i₂) ≡
                      t && ≤-ItemTree i₁ (tip i₂))
               (≤-ItemTree-tip i₁ j)
               refl
      ⟩
    i₁ ≤ j && ≤-ItemTree i₁ (tip i₂)
       ≡⟨ subst (λ t → i₁ ≤ j && ≤-ItemTree i₁ (tip i₂) ≡
                       t && ≤-ItemTree i₁ (tip i₂))
          -- i₁ ≤ j because by hypothesis we have i₁ ≤ (tip j).
                (trans (sym $ ≤-ItemTree-tip i₁ j) i₁≤t)
                refl
       ⟩
    true && ≤-ItemTree i₁ (tip i₂)
      ≡⟨ subst (λ t → true && ≤-ItemTree i₁ (tip i₂) ≡ true && t)
               (≤-ItemTree-tip i₁ i₂)
               refl
      ⟩
      true && i₁ ≤ i₂
      ≡⟨ subst (λ t → true && i₁ ≤ i₂ ≡ true && t)
               i₁≤i₂
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                       (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  prf₁ j>i₂ =
    ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂) ≡
                      ≤-ItemTree i₁ t)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    ≤-ItemTree i₁ (if (j ≤ i₂)
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
    ≡⟨ subst (λ t → ≤-ItemTree i₁ (if (j ≤ i₂)
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)) ≡
                    ≤-ItemTree i₁ (if t
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)))
                (x>y→x≰y Nj Ni₂ j>i₂)
                refl
       ⟩
    ≤-ItemTree i₁ (if false
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (if false
                                        then (node t₁ j (toTree · i₂ · t₂))
                                        else (node (toTree · i₂ · t₁) j t₂)) ≡
                      ≤-ItemTree i₁ t)
               (if-false (node (toTree · i₂ · t₁) j t₂))
               refl
      ⟩
    ≤-ItemTree i₁ (node (toTree · i₂ · t₁) j t₂)
      ≡⟨ ≤-ItemTree-node i₁ (toTree · i₂ · t₁) j t₂ ⟩
      ≤-ItemTree i₁ (toTree · i₂ · t₁) && ≤-ItemTree i₁ t₂
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree · i₂ · t₁) && ≤-ItemTree i₁ t₂ ≡
                      t && ≤-ItemTree i₁ t₂)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
                 (&&-proj₁ (≤-ItemTree-Bool Ni₁ Tt₁)
                           (≤-ItemTree-Bool Ni₁ Tt₂)
                           (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t)))
               refl
      ⟩
    true && ≤-ItemTree i₁ t₂
      ≡⟨ subst (λ t → true && ≤-ItemTree i₁ t₂ ≡ true && t)
               -- i₁ ≤ t₂ because by hypothesis we have i₁ ≤ (node t₁ j t₂).
               (&&-proj₂ (≤-ItemTree-Bool Ni₁ Tt₁)
                         (≤-ItemTree-Bool Ni₁ Tt₂)
                         (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t))
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎

  prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  prf₂ j≤i₂ =
    ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂) ≡
                      ≤-ItemTree i₁ t)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    ≤-ItemTree i₁ (if (j ≤ i₂)
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
    ≡⟨ subst (λ t → ≤-ItemTree i₁ (if (j ≤ i₂)
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)) ≡
                    ≤-ItemTree i₁ (if t
                                      then (node t₁ j (toTree · i₂ · t₂))
                                        else (node (toTree · i₂ · t₁) j t₂)))
                j≤i₂
                refl
       ⟩
    ≤-ItemTree i₁ (if true
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (if true
                                        then (node t₁ j (toTree · i₂ · t₂))
                                        else (node (toTree · i₂ · t₁) j t₂)) ≡
                      ≤-ItemTree i₁ t)
               (if-true (node t₁ j (toTree · i₂ · t₂)))
               refl
      ⟩
    ≤-ItemTree i₁ (node t₁ j (toTree · i₂ · t₂))
      ≡⟨ ≤-ItemTree-node i₁ t₁ j (toTree · i₂ · t₂) ⟩
    ≤-ItemTree i₁ t₁ && ≤-ItemTree i₁ (toTree · i₂ · t₂)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ t₁ && ≤-ItemTree i₁ (toTree · i₂ · t₂) ≡
                      t && ≤-ItemTree i₁ (toTree · i₂ · t₂))
               -- i₁ ≤ t₁ because by hypothesis we have i₁ ≤ (node t₁ j t₂).
               (&&-proj₁ (≤-ItemTree-Bool Ni₁ Tt₁)
                         (≤-ItemTree-Bool Ni₁ Tt₂)
                         (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t))
               refl
      ⟩
    true && ≤-ItemTree i₁ (toTree · i₂ · t₂)
      ≡⟨ subst (λ t → true && ≤-ItemTree i₁ (toTree · i₂ · t₂) ≡ true && t)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
                 (&&-proj₂ (≤-ItemTree-Bool Ni₁ Tt₁)
                           (≤-ItemTree-Bool Ni₁ Tt₂)
                           (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t)))
               refl
      ⟩
    true && true
      ≡⟨ &&-tt ⟩
    true ∎
