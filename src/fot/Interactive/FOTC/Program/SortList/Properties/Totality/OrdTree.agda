------------------------------------------------------------------------------
-- Totality properties respect to OrdTree
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.SortList.Properties.Totality.OrdTree where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.Bool.Properties
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.Properties
open import Interactive.FOTC.Data.Nat.List.Type
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Program.SortList.SortList
open import Interactive.FOTC.Program.SortList.Properties.Totality.Bool
open import Interactive.FOTC.Program.SortList.Properties.Totality.Tree

------------------------------------------------------------------------------
-- Subtrees

-- If (node t₁ i t₂) is ordered then t₁ is ordered.
leftSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                      OrdTree (node t₁ i t₂) → OrdTree t₁
leftSubTree-OrdTree {t₁} {i} {t₂} Tt₁ Ni Tt₂ TOnode =
  ordTree t₁
    ≡⟨ &&-list₂-t₁ (ordTree-Bool Tt₁)
                   (&&-Bool (ordTree-Bool Tt₂)
                            (&&-Bool (le-TreeItem-Bool Tt₁ Ni)
                                     (le-ItemTree-Bool Ni Tt₂)))
                   (trans (sym (ordTree-node t₁ i t₂)) TOnode)
    ⟩
  true ∎

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
rightSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                       OrdTree (node t₁ i t₂) → OrdTree t₂
rightSubTree-OrdTree {t₁} {i} {t₂} Tt₁ Ni Tt₂ TOnode =
  ordTree t₂
    ≡⟨ &&-list₂-t₁
       (ordTree-Bool Tt₂)
         (&&-Bool (le-TreeItem-Bool Tt₁ Ni)
                  (le-ItemTree-Bool Ni Tt₂))
         (&&-list₂-t₂ (ordTree-Bool Tt₁)
                      (&&-Bool (ordTree-Bool Tt₂)
                               (&&-Bool (le-TreeItem-Bool Tt₁ Ni)
                                        (le-ItemTree-Bool Ni Tt₂)))
                      (trans (sym (ordTree-node t₁ i t₂)) TOnode))
    ⟩
  true ∎

------------------------------------------------------------------------------
-- Helper functions

toTree-OrdTree-helper₁ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → i₁ > i₂ →
                         Tree t →
                         ≤-TreeItem t i₁ →
                         ≤-TreeItem (toTree · i₂ · t) i₁
toTree-OrdTree-helper₁ {i₁} {i₂} .{nil} Ni₁ Ni₂ i₁>i₂ tnil _ =
  le-TreeItem (toTree · i₂ · nil) i₁
    ≡⟨ subst (λ t → le-TreeItem (toTree · i₂ · nil) i₁ ≡ le-TreeItem t i₁)
             (toTree-nil i₂)
             refl
    ⟩
  le-TreeItem (tip i₂) i₁
    ≡⟨ le-TreeItem-tip i₂ i₁ ⟩
  le i₂ i₁
    ≡⟨ x<y→x≤y Ni₂ Ni₁ i₁>i₂ ⟩
  true ∎

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ (ttip {j} Nj) t≤i₁ =
  case prf₁ prf₂ (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : j > i₂ → ≤-TreeItem (toTree · i₂ · tip j) i₁
  prf₁ j>i₂ =
    le-TreeItem (toTree · i₂ · tip j) i₁
      ≡⟨ subst (λ t → le-TreeItem (toTree · i₂ · tip j) i₁ ≡
                      le-TreeItem t i₁)
               (toTree-tip i₂ j)
               refl
      ⟩
    le-TreeItem (if (le j i₂)
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → le-TreeItem
                      (if (le j i₂)
                         then (node (tip j) i₂ (tip i₂))
                         else (node (tip i₂) j (tip j))) i₁ ≡
                      le-TreeItem (if t
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁)
               (x>y→x≰y Nj Ni₂ j>i₂)
               refl
      ⟩
    le-TreeItem (if false
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → le-TreeItem (if false
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁ ≡
                      le-TreeItem t i₁)
               (if-false (node (tip i₂) j (tip j)))
               refl
      ⟩
    le-TreeItem (node (tip i₂) j (tip j)) i₁
      ≡⟨ le-TreeItem-node (tip i₂) j (tip j) i₁ ⟩
    le-TreeItem (tip i₂) i₁ && le-TreeItem (tip j) i₁
      ≡⟨ subst (λ t → le-TreeItem (tip i₂) i₁ && le-TreeItem (tip j) i₁ ≡
                      t && le-TreeItem (tip j) i₁)
               (le-TreeItem-tip i₂ i₁)
               refl
      ⟩
    le i₂ i₁ && le-TreeItem (tip j) i₁
       ≡⟨ subst (λ t → le i₂ i₁ && le-TreeItem (tip j) i₁ ≡
                       t && le-TreeItem (tip j) i₁)
                (x<y→x≤y Ni₂ Ni₁ i₁>i₂)
                refl
       ⟩
    true && le-TreeItem (tip j) i₁
      ≡⟨ subst (λ t → true && le-TreeItem (tip j) i₁ ≡ true && t)
               (le-TreeItem-tip j i₁)
               refl
      ⟩
    true && le j i₁
      ≡⟨ subst (λ t → true && le j i₁ ≡ true && t)
               -- j ≤ i₁ because by hypothesis we have (tip j) ≤ i₁.
               (trans (sym (le-TreeItem-tip j i₁)) t≤i₁)
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

  prf₂ : j ≤ i₂ → ≤-TreeItem (toTree · i₂ · tip j) i₁
  prf₂ j≤i₂ =
    le-TreeItem (toTree · i₂ · tip j) i₁
      ≡⟨ subst (λ t → le-TreeItem (toTree · i₂ · tip j) i₁ ≡
                      le-TreeItem t i₁)
               (toTree-tip i₂ j)
               refl
      ⟩
    le-TreeItem (if (le j i₂)
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → le-TreeItem
                      (if (le j i₂)
                         then (node (tip j) i₂ (tip i₂))
                         else (node (tip i₂) j (tip j))) i₁ ≡
                      le-TreeItem (if t
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁)
               j≤i₂
               refl
      ⟩
    le-TreeItem (if true
                   then (node (tip j) i₂ (tip i₂))
                   else (node (tip i₂) j (tip j))) i₁
      ≡⟨ subst (λ t → le-TreeItem (if true
                                     then (node (tip j) i₂ (tip i₂))
                                     else (node (tip i₂) j (tip j))) i₁ ≡
                      le-TreeItem t i₁)
               (if-true (node (tip j) i₂ (tip i₂)))
               refl
         ⟩
    le-TreeItem (node (tip j) i₂ (tip i₂)) i₁
      ≡⟨ le-TreeItem-node (tip j) i₂ (tip i₂) i₁ ⟩
    le-TreeItem (tip j) i₁ && le-TreeItem (tip i₂) i₁
      ≡⟨ subst (λ t → le-TreeItem (tip j) i₁ && le-TreeItem (tip i₂) i₁ ≡
                      t && le-TreeItem (tip i₂) i₁)
               (le-TreeItem-tip j i₁)
               refl
      ⟩
    le j i₁ && le-TreeItem (tip i₂) i₁
      ≡⟨ subst (λ t → le j i₁ && le-TreeItem (tip i₂) i₁ ≡
                      t && le-TreeItem (tip i₂) i₁)
               -- j ≤ i₁ because by hypothesis we have (tip j) ≤ i₁.
               (trans (sym (le-TreeItem-tip j i₁)) t≤i₁)
               refl
      ⟩
    true && le-TreeItem (tip i₂) i₁
      ≡⟨ subst (λ t → true && le-TreeItem (tip i₂) i₁ ≡ true && t)
               (le-TreeItem-tip i₂ i₁)
               refl
      ⟩
    true && le i₂ i₁
      ≡⟨ subst (λ t → true && le i₂ i₁ ≡ true && t)
               (x<y→x≤y Ni₂ Ni₁ i₁>i₂)
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                       (tnode {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  case prf₁ prf₂ (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : j > i₂ → ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  prf₁ j>i₂ =
    le-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
      ≡⟨ subst (λ t → le-TreeItem (toTree · i₂ · node t₁ j t₂) i₁ ≡
                      le-TreeItem t i₁)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    le-TreeItem (if (le j i₂)
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → le-TreeItem
                        (if (le j i₂)
                           then (node t₁ j (toTree · i₂ · t₂))
                           else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      le-TreeItem
                        (if t
                           then (node t₁ j (toTree · i₂ · t₂))
                           else (node (toTree · i₂ · t₁) j t₂)) i₁)
               (x>y→x≰y Nj Ni₂ j>i₂)
               refl
      ⟩
    le-TreeItem (if false
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → le-TreeItem (if false
                                     then (node t₁ j (toTree · i₂ · t₂))
                                     else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      le-TreeItem t i₁)
               (if-false (node (toTree · i₂ · t₁) j t₂))
               refl
      ⟩
    le-TreeItem (node (toTree · i₂ · t₁) j t₂) i₁
      ≡⟨ le-TreeItem-node (toTree · i₂ · t₁) j t₂ i₁ ⟩
    le-TreeItem (toTree · i₂ · t₁) i₁ && le-TreeItem t₂ i₁
      ≡⟨ subst (λ t → le-TreeItem (toTree · i₂ · t₁) i₁ &&
                      le-TreeItem t₂ i₁                 ≡
                      t                                &&
                      le-TreeItem t₂ i₁)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₁
                 (&&-list₂-t₁ (le-TreeItem-Bool Tt₁ Ni₁)
                              (le-TreeItem-Bool Tt₂ Ni₁)
                              (trans (sym (le-TreeItem-node t₁ j t₂ i₁)) t≤i₁)))
               refl
      ⟩
    true && le-TreeItem t₂ i₁
      ≡⟨ subst (λ t → true && le-TreeItem t₂ i₁ ≡ true && t)
               -- t₂ ≤ i₁ because by hypothesis we have (node t₁ j t₂) ≤ i₁.
               (&&-list₂-t₂ (le-TreeItem-Bool Tt₁ Ni₁)
                            (le-TreeItem-Bool Tt₂ Ni₁)
                            (trans (sym (le-TreeItem-node t₁ j t₂ i₁)) t≤i₁))
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

  prf₂ : j ≤ i₂ → ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  prf₂ j≤i₂ =
    le-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
      ≡⟨ subst (λ t → le-TreeItem (toTree · i₂ · node t₁ j t₂) i₁ ≡
                      le-TreeItem t i₁)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    le-TreeItem (if (le j i₂)
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → le-TreeItem
                        (if (le j i₂)
                           then (node t₁ j (toTree · i₂ · t₂))
                           else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      le-TreeItem
                        (if t
                           then (node t₁ j (toTree · i₂ · t₂))
                           else (node (toTree · i₂ · t₁) j t₂)) i₁)
               (j≤i₂)
               refl
      ⟩
    le-TreeItem (if true
                   then (node t₁ j (toTree · i₂ · t₂))
                   else (node (toTree · i₂ · t₁) j t₂)) i₁
      ≡⟨ subst (λ t → le-TreeItem (if true
                                     then (node t₁ j (toTree · i₂ · t₂))
                                     else (node (toTree · i₂ · t₁) j t₂)) i₁ ≡
                      le-TreeItem t i₁)
               (if-true (node t₁ j (toTree · i₂ · t₂)))
               refl
      ⟩
    le-TreeItem (node t₁ j (toTree · i₂ · t₂)) i₁
      ≡⟨ le-TreeItem-node t₁ j (toTree · i₂ · t₂) i₁ ⟩
    le-TreeItem t₁ i₁ && le-TreeItem (toTree · i₂ · t₂) i₁
      ≡⟨ subst (λ t → le-TreeItem t₁ i₁ && le-TreeItem (toTree · i₂ · t₂) i₁ ≡
                      t &&  le-TreeItem (toTree · i₂ · t₂) i₁)
               -- t₁ ≤ i₁ because by hypothesis we have (node t₁ j t₂) ≤ i₁.
               (&&-list₂-t₁ (le-TreeItem-Bool Tt₁ Ni₁)
                            (le-TreeItem-Bool Tt₂ Ni₁)
                            (trans (sym (le-TreeItem-node t₁ j t₂ i₁)) t≤i₁))
               refl
      ⟩
    true && le-TreeItem (toTree · i₂ · t₂) i₁
      ≡⟨ subst (λ t → true && le-TreeItem (toTree · i₂ · t₂) i₁ ≡
                      true && t)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₂
                 (&&-list₂-t₂ (le-TreeItem-Bool Tt₁ Ni₁)
                              (le-TreeItem-Bool Tt₂ Ni₁)
                              (trans (sym (le-TreeItem-node t₁ j t₂ i₁)) t≤i₁)))
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

------------------------------------------------------------------------------

toTree-OrdTree-helper₂ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → i₁ ≤ i₂ →
                         Tree t →
                         ≤-ItemTree i₁ t →
                         ≤-ItemTree i₁ (toTree · i₂ · t)
toTree-OrdTree-helper₂ {i₁} {i₂} .{nil} _ _ i₁≤i₂ tnil _ =
  le-ItemTree i₁ (toTree · i₂ · nil)
    ≡⟨ subst (λ t → le-ItemTree i₁ (toTree · i₂ · nil) ≡ le-ItemTree i₁ t)
             (toTree-nil i₂)
             refl
    ⟩
  le-ItemTree i₁ (tip i₂)
    ≡⟨ le-ItemTree-tip i₁ i₂ ⟩
  le i₁ i₂
    ≡⟨ i₁≤i₂ ⟩
  true ∎

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (ttip {j} Nj) i₁≤t =
  case prf₁ prf₂ (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : j > i₂ → ≤-ItemTree i₁ (toTree · i₂ · tip j)
  prf₁ j>i₂ =
    le-ItemTree i₁ (toTree · i₂ · tip j)
      ≡⟨ subst (λ t → le-ItemTree i₁ (toTree · i₂ · tip j) ≡
                      le-ItemTree i₁ t)
               (toTree-tip i₂ j)
               refl
      ⟩
    le-ItemTree i₁ (if (le j i₂)
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
      ≡⟨ subst (λ t → le-ItemTree i₁ (if (le j i₂)
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                      le-ItemTree i₁ (if t
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))))
             (x>y→x≰y Nj Ni₂ j>i₂)
             refl
       ⟩
    le-ItemTree i₁ (if false
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
    ≡⟨ subst (λ t → le-ItemTree i₁ (if false
                                      then (node (tip j) i₂ (tip i₂))
                                      else (node (tip i₂) j (tip j))) ≡
                    le-ItemTree i₁ t)
                (if-false (node (tip i₂) j (tip j)))
                refl
       ⟩
    le-ItemTree i₁ (node (tip i₂) j (tip j))
      ≡⟨ le-ItemTree-node i₁ (tip i₂) j (tip j) ⟩
    le-ItemTree i₁ (tip i₂) && le-ItemTree i₁ (tip j)
      ≡⟨ subst (λ t → le-ItemTree i₁ (tip i₂) && le-ItemTree i₁ (tip j) ≡
                      t && le-ItemTree i₁ (tip j))
               (le-ItemTree-tip i₁ i₂)
               refl
      ⟩
    le i₁ i₂ && le-ItemTree i₁ (tip j)
       ≡⟨ subst (λ t → le i₁ i₂ && le-ItemTree i₁ (tip j) ≡
                       t && le-ItemTree i₁ (tip j))
                i₁≤i₂
                refl
        ⟩
    true && le-ItemTree i₁ (tip j)
      ≡⟨ subst (λ t → true && le-ItemTree i₁ (tip j) ≡ true && t)
               (le-ItemTree-tip i₁ j)
               refl
      ⟩
    true && le i₁ j
      ≡⟨ subst (λ t → true && le i₁ j ≡ true && t)
               -- i₁ ≤ j because by hypothesis we have i₁ ≤ (tip j).
               (trans (sym (le-ItemTree-tip i₁ j)) i₁≤t)
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

  prf₂ : j ≤ i₂ → ≤-ItemTree i₁ (toTree · i₂ · tip j)
  prf₂ j≤i₂ =
    le-ItemTree i₁ (toTree · i₂ · tip j)
      ≡⟨ subst (λ t → le-ItemTree i₁ (toTree · i₂ · tip j) ≡
                      le-ItemTree i₁ t)
               (toTree-tip i₂ j)
               refl
      ⟩
    le-ItemTree i₁ (if (le j i₂)
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
      ≡⟨ subst (λ t → le-ItemTree i₁ (if (le j i₂)
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                      le-ItemTree i₁ (if t
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))))
               j≤i₂
               refl
        ⟩
    le-ItemTree i₁ (if true
                      then (node (tip j) i₂ (tip i₂))
                      else (node (tip i₂) j (tip j)))
      ≡⟨ subst (λ t → le-ItemTree i₁ (if true
                                        then (node (tip j) i₂ (tip i₂))
                                        else (node (tip i₂) j (tip j))) ≡
                      le-ItemTree i₁ t)
               (if-true (node (tip j) i₂ (tip i₂)))
               refl
      ⟩
    le-ItemTree i₁ (node (tip j) i₂ (tip i₂))
      ≡⟨ le-ItemTree-node i₁ (tip j) i₂ (tip i₂) ⟩
    le-ItemTree i₁ (tip j) && le-ItemTree i₁ (tip i₂)
      ≡⟨ subst (λ t → le-ItemTree i₁ (tip j) && le-ItemTree i₁ (tip i₂) ≡
                      t && le-ItemTree i₁ (tip i₂))
               (le-ItemTree-tip i₁ j)
               refl
      ⟩
    le i₁ j && le-ItemTree i₁ (tip i₂)
       ≡⟨ subst (λ t → le i₁ j && le-ItemTree i₁ (tip i₂) ≡
                       t && le-ItemTree i₁ (tip i₂))
          -- i₁ ≤ j because by hypothesis we have i₁ ≤ (tip j).
                (trans (sym (le-ItemTree-tip i₁ j)) i₁≤t)
                refl
       ⟩
    true && le-ItemTree i₁ (tip i₂)
      ≡⟨ subst (λ t → true && le-ItemTree i₁ (tip i₂) ≡ true && t)
               (le-ItemTree-tip i₁ i₂)
               refl
      ⟩
      true && le i₁ i₂
      ≡⟨ subst (λ t → true && le i₁ i₂ ≡ true && t)
               i₁≤i₂
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                       (tnode {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  case prf₁ prf₂ (x>y∨x≤y Nj Ni₂)
  where
  prf₁ : j > i₂ → ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  prf₁ j>i₂ =
    le-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
      ≡⟨ subst (λ t → le-ItemTree i₁ (toTree · i₂ · node t₁ j t₂) ≡
                      le-ItemTree i₁ t)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    le-ItemTree i₁ (if (le j i₂)
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
    ≡⟨ subst (λ t → le-ItemTree i₁ (if (le j i₂)
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)) ≡
                    le-ItemTree i₁ (if t
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)))
                (x>y→x≰y Nj Ni₂ j>i₂)
                refl
       ⟩
    le-ItemTree i₁ (if false
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
      ≡⟨ subst (λ t → le-ItemTree i₁ (if false
                                        then (node t₁ j (toTree · i₂ · t₂))
                                        else (node (toTree · i₂ · t₁) j t₂)) ≡
                      le-ItemTree i₁ t)
               (if-false (node (toTree · i₂ · t₁) j t₂))
               refl
      ⟩
    le-ItemTree i₁ (node (toTree · i₂ · t₁) j t₂)
      ≡⟨ le-ItemTree-node i₁ (toTree · i₂ · t₁) j t₂ ⟩
      le-ItemTree i₁ (toTree · i₂ · t₁) && le-ItemTree i₁ t₂
      ≡⟨ subst (λ t → le-ItemTree i₁ (toTree · i₂ · t₁) && le-ItemTree i₁ t₂ ≡
                      t && le-ItemTree i₁ t₂)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
                 (&&-list₂-t₁ (le-ItemTree-Bool Ni₁ Tt₁)
                              (le-ItemTree-Bool Ni₁ Tt₂)
                              (trans (sym (le-ItemTree-node i₁ t₁ j t₂)) i₁≤t)))
               refl
      ⟩
    true && le-ItemTree i₁ t₂
      ≡⟨ subst (λ t → true && le-ItemTree i₁ t₂ ≡ true && t)
               -- i₁ ≤ t₂ because by hypothesis we have i₁ ≤ (node t₁ j t₂).
               (&&-list₂-t₂ (le-ItemTree-Bool Ni₁ Tt₁)
                            (le-ItemTree-Bool Ni₁ Tt₂)
                            (trans (sym (le-ItemTree-node i₁ t₁ j t₂)) i₁≤t))
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎

  prf₂ : j ≤ i₂ → ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  prf₂ j≤i₂ =
    le-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
      ≡⟨ subst (λ t → le-ItemTree i₁ (toTree · i₂ · node t₁ j t₂) ≡
                      le-ItemTree i₁ t)
               (toTree-node i₂ t₁ j t₂)
               refl
      ⟩
    le-ItemTree i₁ (if (le j i₂)
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
    ≡⟨ subst (λ t → le-ItemTree i₁ (if (le j i₂)
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)) ≡
                    le-ItemTree i₁ (if t
                                      then (node t₁ j (toTree · i₂ · t₂))
                                      else (node (toTree · i₂ · t₁) j t₂)))
                j≤i₂
                refl
       ⟩
    le-ItemTree i₁ (if true
                      then (node t₁ j (toTree · i₂ · t₂))
                      else (node (toTree · i₂ · t₁) j t₂))
      ≡⟨ subst (λ t → le-ItemTree i₁ (if true
                                        then (node t₁ j (toTree · i₂ · t₂))
                                        else (node (toTree · i₂ · t₁) j t₂)) ≡
                      le-ItemTree i₁ t)
               (if-true (node t₁ j (toTree · i₂ · t₂)))
               refl
      ⟩
    le-ItemTree i₁ (node t₁ j (toTree · i₂ · t₂))
      ≡⟨ le-ItemTree-node i₁ t₁ j (toTree · i₂ · t₂) ⟩
    le-ItemTree i₁ t₁ && le-ItemTree i₁ (toTree · i₂ · t₂)
      ≡⟨ subst (λ t → le-ItemTree i₁ t₁ && le-ItemTree i₁ (toTree · i₂ · t₂) ≡
                      t && le-ItemTree i₁ (toTree · i₂ · t₂))
               -- i₁ ≤ t₁ because by hypothesis we have i₁ ≤ (node t₁ j t₂).
               (&&-list₂-t₁ (le-ItemTree-Bool Ni₁ Tt₁)
                            (le-ItemTree-Bool Ni₁ Tt₂)
                            (trans (sym (le-ItemTree-node i₁ t₁ j t₂)) i₁≤t))
               refl
      ⟩
    true && le-ItemTree i₁ (toTree · i₂ · t₂)
      ≡⟨ subst (λ t → true && le-ItemTree i₁ (toTree · i₂ · t₂) ≡ true && t)
               -- Inductive hypothesis.
               (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
                 (&&-list₂-t₂ (le-ItemTree-Bool Ni₁ Tt₁)
                              (le-ItemTree-Bool Ni₁ Tt₂)
                              (trans (sym (le-ItemTree-node i₁ t₁ j t₂)) i₁≤t)))
               refl
      ⟩
    true && true
      ≡⟨ t&&x≡x true ⟩
    true ∎
