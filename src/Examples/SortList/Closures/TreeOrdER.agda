------------------------------------------------------------------------------
-- Closures properties respect to TreeOrd (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.TreeOrdER where

open import LTC.Base
open import LTC.BaseER using ( subst )

open import Examples.SortList.SortList
  using ( ≤-ItemTree ; ≤-ItemTree-node ; ≤-ItemTree-tip
        ; ≤-TreeItem ; ≤-TreeItem-node ; ≤-TreeItem-tip
        ; LE-ItemTree
        ; isTreeOrd ; isTreeOrd-nilTree ; isTreeOrd-node ; isTreeOrd-tip
        ; LE-TreeItem
        ; makeTree
        ; nilTree ; node ; tip
        ; toTree ; toTree-nilTree ; toTree-node ; toTree-tip
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        ; TreeOrd
        )
open import Examples.SortList.Closures.BoolER
  using ( ≤-ItemTree-Bool
        ; ≤-TreeItem-Bool
        ; isTreeOrd-Bool
        )
open import Examples.SortList.Closures.TreeER using ( makeTree-Tree )

import Lib.Relation.Binary.EqReasoning
open module TreeOrd-ER = Lib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

open import LTC.Data.Bool using ( _&&_ ; &&-tt )
open import LTC.Data.Bool.PropertiesER
  using ( &&-Bool
        ; x&&y≡true→x≡true
        ; x&&y≡true→y≡true
        ; w&&x&&y&&z≡true→y≡true
        ; w&&x&&y&&z≡true→z≡true
        )
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesER
  using ( x<y→x≤y
        ; x>y→x≰y
        ; x>y∨x≤y
        ; x≤x
        )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type using ( N )
open import LTC.Data.List using ( foldr ; foldr-[] ; foldr-∷ )

------------------------------------------------------------------------------
-- Subtrees

-- If (node t₁ i t₂) is ordered then t₁ is ordered.
leftSubTree-TreeOrd : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ →
                      TreeOrd (node t₁ i t₂) → TreeOrd t₁
leftSubTree-TreeOrd {t₁} {i} {t₂} Tt₁ Ni Tt₂ TOnode =
  begin
    isTreeOrd t₁
      ≡⟨ x&&y≡true→x≡true (isTreeOrd-Bool Tt₁)
                          (&&-Bool (isTreeOrd-Bool Tt₂)
                                   (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                            (≤-ItemTree-Bool Ni Tt₂)))
                          (trans (sym (isTreeOrd-node t₁ i t₂)) TOnode) ⟩
    true
  ∎

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
rightSubTree-TreeOrd : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ →
                       TreeOrd (node t₁ i t₂) → TreeOrd t₂
rightSubTree-TreeOrd {t₁} {i} {t₂} Tt₁ Ni Tt₂ TOnode =
  begin
    isTreeOrd t₂
      ≡⟨ x&&y≡true→x≡true
           (isTreeOrd-Bool Tt₂)
           (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                    (≤-ItemTree-Bool Ni Tt₂))
           (x&&y≡true→y≡true (isTreeOrd-Bool Tt₁)
                             (&&-Bool (isTreeOrd-Bool Tt₂)
                                      (&&-Bool (≤-TreeItem-Bool Tt₁ Ni)
                                               (≤-ItemTree-Bool Ni Tt₂)))
                             (trans (sym (isTreeOrd-node t₁ i t₂)) TOnode))
      ⟩
    true
  ∎

------------------------------------------------------------------------------
-- Auxiliar functions

toTree-TreeOrd-aux₁ : {i₁ i₂ : D} → N i₁ → N i₂ → GT i₁ i₂ →
                      {t : D} → Tree t →
                      LE-TreeItem t i₁ →
                      LE-TreeItem (toTree ∙ i₂ ∙ t) i₁
toTree-TreeOrd-aux₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ .{nilTree} nilT _ =
  begin
    ≤-TreeItem (toTree ∙ i₂ ∙ nilTree) i₁
      ≡⟨ subst (λ t → ≤-TreeItem (toTree ∙ i₂ ∙ nilTree) i₁ ≡ ≤-TreeItem t i₁)
               (toTree-nilTree i₂)
               refl
      ⟩
    ≤-TreeItem (tip i₂) i₁ ≡⟨ ≤-TreeItem-tip i₂ i₁ ⟩
    i₂ ≤ i₁               ≡⟨ x<y→x≤y Ni₂ Ni₁ i₁>i₂ ⟩
    true
  ∎

toTree-TreeOrd-aux₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ (tipT {j} Nj) t≤i₁ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
    prf₁ : GT j i₂ → LE-TreeItem (toTree ∙ i₂ ∙ tip j) i₁
    prf₁ j>i₂ =
      begin
        ≤-TreeItem (toTree ∙ i₂ ∙ tip j) i₁
          ≡⟨ subst (λ t → ≤-TreeItem (toTree ∙ i₂ ∙ tip j) i₁ ≡
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
                   (trans (sym (≤-TreeItem-tip j i₁)) t≤i₁)
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

    prf₂ : LE j i₂ → LE-TreeItem (toTree ∙ i₂ ∙ tip j) i₁
    prf₂ j≤i₂ =
      begin
        ≤-TreeItem (toTree ∙ i₂ ∙ tip j) i₁
          ≡⟨ subst (λ t → ≤-TreeItem (toTree ∙ i₂ ∙ tip j) i₁ ≡
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
                   (j≤i₂)
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
                   refl ⟩
        j ≤ i₁ && ≤-TreeItem (tip i₂) i₁
          ≡⟨ subst (λ t → j ≤ i₁ && ≤-TreeItem (tip i₂) i₁ ≡
                          t && ≤-TreeItem (tip i₂) i₁)
                   -- j ≤ i₁ because by hypothesis we have (tip j) ≤ i₁.
                   (trans (sym (≤-TreeItem-tip j i₁)) t≤i₁)
                   refl
          ⟩
        true && ≤-TreeItem (tip i₂) i₁
          ≡⟨ subst (λ t → true && ≤-TreeItem (tip i₂) i₁ ≡ true && t)
                   (≤-TreeItem-tip i₂ i₁)
                   refl ⟩
        true && i₂ ≤ i₁
          ≡⟨ subst (λ t → true && i₂ ≤ i₁ ≡ true && t)
                   (x<y→x≤y Ni₂ Ni₁ i₁>i₂)
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

toTree-TreeOrd-aux₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                    (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
    prf₁ : GT j i₂ → LE-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁
    prf₁ j>i₂ =
      begin
        ≤-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁
          ≡⟨ subst (λ t → ≤-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁ ≡
                          ≤-TreeItem t i₁)
                   (toTree-node i₂ t₁ j t₂)
                   refl
          ⟩
        ≤-TreeItem (if (j ≤ i₂)
                       then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                       else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁
          ≡⟨ subst (λ t → ≤-TreeItem
                            (if (j ≤ i₂)
                                then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁ ≡
                            ≤-TreeItem
                              (if t
                                  then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                  else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁)
                   (x>y→x≰y Nj Ni₂ j>i₂)
                   refl
          ⟩
        ≤-TreeItem (if false
                       then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                       else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁
          ≡⟨ subst (λ t → ≤-TreeItem (if false
                                         then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                         else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁ ≡
                          ≤-TreeItem t i₁)
                   (if-false (node (toTree ∙ i₂ ∙ t₁) j t₂))
                   refl
          ⟩
        ≤-TreeItem (node (toTree ∙ i₂ ∙ t₁) j t₂) i₁
          ≡⟨ ≤-TreeItem-node (toTree ∙ i₂ ∙ t₁) j t₂ i₁ ⟩
        ≤-TreeItem (toTree ∙ i₂ ∙ t₁) i₁ && ≤-TreeItem t₂ i₁
          ≡⟨ subst (λ t → ≤-TreeItem (toTree ∙ i₂ ∙ t₁) i₁ &&
                          ≤-TreeItem t₂ i₁                 ≡
                          t                                &&
                          ≤-TreeItem t₂ i₁)
                   -- Inductive hypothesis.
                   (toTree-TreeOrd-aux₁ Ni₁ Ni₂ i₁>i₂ Tt₁
                     (x&&y≡true→x≡true (≤-TreeItem-Bool Tt₁ Ni₁)
                                       (≤-TreeItem-Bool Tt₂ Ni₁)
                                       (trans (sym (≤-TreeItem-node t₁ j t₂ i₁))
                                              t≤i₁)))
                   refl
          ⟩
        true && ≤-TreeItem t₂ i₁
          ≡⟨ subst (λ t → true && ≤-TreeItem t₂ i₁ ≡ true && t)
                   -- t₂ ≤ i₁ because by hypothesis we have (node t₁ j t₂) ≤ i₁.
                   (x&&y≡true→y≡true (≤-TreeItem-Bool Tt₁ Ni₁)
                                     (≤-TreeItem-Bool Tt₂ Ni₁)
                                     (trans (sym (≤-TreeItem-node t₁ j t₂ i₁))
                                            t≤i₁))
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

    prf₂ : LE j i₂ → LE-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁
    prf₂ j≤i₂ =
      begin
        ≤-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁
          ≡⟨ subst (λ t → ≤-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁ ≡
                          ≤-TreeItem t i₁)
                   (toTree-node i₂ t₁ j t₂)
                   refl
          ⟩
        ≤-TreeItem (if (j ≤ i₂)
                       then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                       else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁
          ≡⟨ subst (λ t → ≤-TreeItem
                            (if (j ≤ i₂)
                                then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁ ≡
                          ≤-TreeItem
                            (if t
                                then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁)
                   (j≤i₂)
                   refl
          ⟩
        ≤-TreeItem (if true
                       then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                       else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁

          ≡⟨ subst (λ t → ≤-TreeItem (if true
                                         then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                         else (node (toTree ∙ i₂ ∙ t₁) j t₂)) i₁ ≡
                          ≤-TreeItem t i₁)
                   (if-true (node t₁ j (toTree ∙ i₂ ∙ t₂)))
                   refl
          ⟩
        ≤-TreeItem (node t₁ j (toTree ∙ i₂ ∙ t₂)) i₁
          ≡⟨ ≤-TreeItem-node t₁ j (toTree ∙ i₂ ∙ t₂) i₁ ⟩
        ≤-TreeItem t₁ i₁ && ≤-TreeItem (toTree ∙ i₂ ∙ t₂) i₁
          ≡⟨ subst (λ t → ≤-TreeItem t₁ i₁ && ≤-TreeItem (toTree ∙ i₂ ∙ t₂) i₁ ≡
                          t &&  ≤-TreeItem (toTree ∙ i₂ ∙ t₂) i₁)
                   -- t₁ ≤ i₁ because by hypothesis we have (node t₁ j t₂) ≤ i₁.
                   (x&&y≡true→x≡true (≤-TreeItem-Bool Tt₁ Ni₁)
                                     (≤-TreeItem-Bool Tt₂ Ni₁)
                                     (trans (sym (≤-TreeItem-node t₁ j t₂ i₁))
                                            t≤i₁))
                   refl
          ⟩
        true && ≤-TreeItem (toTree ∙ i₂ ∙ t₂) i₁
          ≡⟨ subst (λ t → true && ≤-TreeItem (toTree ∙ i₂ ∙ t₂) i₁ ≡
                          true && t)
                   -- Inductive hypothesis.
                   (toTree-TreeOrd-aux₁ Ni₁ Ni₂ i₁>i₂ Tt₂
                     (x&&y≡true→y≡true (≤-TreeItem-Bool Tt₁ Ni₁)
                                       (≤-TreeItem-Bool Tt₂ Ni₁)
                                       (trans (sym (≤-TreeItem-node t₁ j t₂ i₁))
                                              t≤i₁)))
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
        true
      ∎

------------------------------------------------------------------------------
toTree-TreeOrd-aux₂ : {i₁ i₂ : D} → N i₁ → N i₂ → LE i₁ i₂ →
                      {t : D} → Tree t →
                      LE-ItemTree i₁ t →
                      LE-ItemTree i₁ (toTree ∙ i₂ ∙ t)
toTree-TreeOrd-aux₂ {i₁} {i₂} _ _ i₁≤i₂ .{nilTree} nilT _ =
  begin
    ≤-ItemTree i₁ (toTree ∙ i₂ ∙ nilTree)
      ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree ∙ i₂ ∙ nilTree) ≡ ≤-ItemTree i₁ t)
               (toTree-nilTree i₂)
               refl
      ⟩
    ≤-ItemTree i₁ (tip i₂) ≡⟨ ≤-ItemTree-tip i₁ i₂ ⟩
    i₁ ≤ i₂               ≡⟨ i₁≤i₂ ⟩
    true
  ∎

toTree-TreeOrd-aux₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (tipT {j} Nj) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
    prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree ∙ i₂ ∙ tip j)
    prf₁ j>i₂ =
      begin
        ≤-ItemTree i₁ (toTree ∙ i₂ ∙ tip j)
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree ∙ i₂ ∙ tip j) ≡
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
                   (trans (sym (≤-ItemTree-tip i₁ j)) i₁≤t)
                   refl
          ⟩
        true && true ≡⟨ &&-tt ⟩
      true
      ∎

    prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree ∙ i₂ ∙ tip j)
    prf₂ j≤i₂ =
      begin
        ≤-ItemTree i₁ (toTree ∙ i₂ ∙ tip j)
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree ∙ i₂ ∙ tip j) ≡
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
                   (j≤i₂)
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
                   (trans (sym (≤-ItemTree-tip i₁ j)) i₁≤t)
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
        true && true ≡⟨ &&-tt ⟩
      true
      ∎

toTree-TreeOrd-aux₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                    (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
    prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂)
    prf₁ j>i₂ =
      begin
        ≤-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂)
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂) ≡
                          ≤-ItemTree i₁ t)
                   (toTree-node i₂ t₁ j t₂)
                   refl
          ⟩
        ≤-ItemTree i₁ (if (j ≤ i₂)
                          then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                          else (node (toTree ∙ i₂ ∙ t₁) j t₂))
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (if (j ≤ i₂)
                                            then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                            else (node (toTree ∙ i₂ ∙ t₁) j t₂)) ≡
                          ≤-ItemTree i₁ (if t
                                            then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                            else (node (toTree ∙ i₂ ∙ t₁) j t₂)))
                   (x>y→x≰y Nj Ni₂ j>i₂)
                   refl
          ⟩
        ≤-ItemTree i₁ (if false
                           then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                           else (node (toTree ∙ i₂ ∙ t₁) j t₂))
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (if false
                                        then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                        else (node (toTree ∙ i₂ ∙ t₁) j t₂)) ≡
                          ≤-ItemTree i₁ t)
                   (if-false (node (toTree ∙ i₂ ∙ t₁) j t₂))
                   refl
          ⟩
        ≤-ItemTree i₁ (node (toTree ∙ i₂ ∙ t₁) j t₂)
          ≡⟨ ≤-ItemTree-node i₁ (toTree ∙ i₂ ∙ t₁) j t₂ ⟩
         ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₁) && ≤-ItemTree i₁ t₂
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₁) && ≤-ItemTree i₁ t₂ ≡
                          t && ≤-ItemTree i₁ t₂)
                   -- Inductive hypothesis.
                   (toTree-TreeOrd-aux₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
                     (x&&y≡true→x≡true (≤-ItemTree-Bool Ni₁ Tt₁)
                                       (≤-ItemTree-Bool Ni₁ Tt₂)
                                       (trans (sym (≤-ItemTree-node i₁ t₁ j t₂))
                                              i₁≤t)))
                   refl
          ⟩
        true && ≤-ItemTree i₁ t₂
          ≡⟨ subst (λ t → true && ≤-ItemTree i₁ t₂ ≡ true && t)
                   -- i₁ ≤ t₂ because by hypothesis we have i₁ ≤ (node t₁ j t₂).
                   (x&&y≡true→y≡true (≤-ItemTree-Bool Ni₁ Tt₁)
                                     (≤-ItemTree-Bool Ni₁ Tt₂)
                                     (trans (sym (≤-ItemTree-node i₁ t₁ j t₂))
                                            i₁≤t))
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
      true
      ∎

    prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂)
    prf₂ j≤i₂ =
      begin
        ≤-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂)
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂) ≡
                          ≤-ItemTree i₁ t)
                   (toTree-node i₂ t₁ j t₂)
                   refl
          ⟩
        ≤-ItemTree i₁ (if (j ≤ i₂)
                          then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                          else (node (toTree ∙ i₂ ∙ t₁) j t₂))
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (if (j ≤ i₂)
                                            then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                            else (node (toTree ∙ i₂ ∙ t₁) j t₂)) ≡
                          ≤-ItemTree i₁ (if t
                                            then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                            else (node (toTree ∙ i₂ ∙ t₁) j t₂)))
                   (j≤i₂)
                   refl
          ⟩
        ≤-ItemTree i₁ (if true
                           then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                           else (node (toTree ∙ i₂ ∙ t₁) j t₂))
          ≡⟨ subst (λ t → ≤-ItemTree i₁ (if true
                                        then (node t₁ j (toTree ∙ i₂ ∙ t₂))
                                        else (node (toTree ∙ i₂ ∙ t₁) j t₂)) ≡
                          ≤-ItemTree i₁ t)
                   (if-true (node t₁ j (toTree ∙ i₂ ∙ t₂)))
                   refl
          ⟩
        ≤-ItemTree i₁ (node t₁ j (toTree ∙ i₂ ∙ t₂))
          ≡⟨ ≤-ItemTree-node i₁ t₁ j (toTree ∙ i₂ ∙ t₂) ⟩
        ≤-ItemTree i₁ t₁ && ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₂)
          ≡⟨ subst (λ t → ≤-ItemTree i₁ t₁ && ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₂) ≡
                          t && ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₂))
                   -- i₁ ≤ t₁ because by hypothesis we have i₁ ≤ (node t₁ j t₂).
                   (x&&y≡true→x≡true (≤-ItemTree-Bool Ni₁ Tt₁)
                                     (≤-ItemTree-Bool Ni₁ Tt₂)
                                     (trans (sym (≤-ItemTree-node i₁ t₁ j t₂))
                                            i₁≤t))
                   refl
          ⟩
        true && ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₂)
          ≡⟨ subst (λ t → true && ≤-ItemTree i₁ (toTree ∙ i₂ ∙ t₂) ≡ true && t)
                   -- Inductive hypothesis.
                   (toTree-TreeOrd-aux₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
                     (x&&y≡true→y≡true (≤-ItemTree-Bool Ni₁ Tt₁)
                                       (≤-ItemTree-Bool Ni₁ Tt₂)
                                       (trans (sym (≤-ItemTree-node i₁ t₁ j t₂))
                                              i₁≤t)))
                   refl
          ⟩
        true && true
          ≡⟨ &&-tt ⟩
      true
      ∎

------------------------------------------------------------------------------
-- If t is ordered then toTree i t is ordered.
toTree-TreeOrd : {item t : D} → N item → Tree t → TreeOrd t →
                 TreeOrd (toTree ∙ item ∙ t)
toTree-TreeOrd {item} Nitem nilT _ = prf
  where
    postulate prf : TreeOrd (toTree ∙ item ∙ nilTree)

toTree-TreeOrd {item} Nitem (tipT {i} Ni) _ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Ni Nitem)
  where
    prf₁ : GT i item → TreeOrd (toTree ∙ item ∙ tip i)
    prf₁ i>item =
      begin
        isTreeOrd (toTree ∙ item ∙ tip i)
          ≡⟨ subst (λ t → isTreeOrd (toTree ∙ item ∙ tip i) ≡ isTreeOrd t)
                   (toTree-tip item i)
                   refl
          ⟩
        isTreeOrd (if (i ≤ item)
                      then (node (tip i) item (tip item))
                      else (node (tip item) i (tip i)))
           ≡⟨ subst (λ t → isTreeOrd (if (i ≤ item)
                                         then (node (tip i) item (tip item))
                                         else (node (tip item) i (tip i))) ≡
                           isTreeOrd (if t
                                         then (node (tip i) item (tip item))
                                         else (node (tip item) i (tip i))))
                    (x>y→x≰y Ni Nitem i>item)
                    refl
           ⟩
        isTreeOrd (if false
                      then (node (tip i) item (tip item))
                      else (node (tip item) i (tip i)))
          ≡⟨ subst (λ t → isTreeOrd (if false
                                        then (node (tip i) item (tip item))
                                        else (node (tip item) i (tip i))) ≡
                                     isTreeOrd t)
                   (if-false (node (tip item) i (tip i)))
                   refl
          ⟩
        isTreeOrd (node (tip item) i (tip i))
          ≡⟨ isTreeOrd-node (tip item) i (tip i) ⟩
        isTreeOrd (tip item)    &&
        isTreeOrd (tip i)       &&
        ≤-TreeItem (tip item) i &&
        ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → isTreeOrd (tip item)    &&
                          isTreeOrd (tip i)       &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i)    ≡
                          t                       &&
                          isTreeOrd (tip i)       &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i))
                   (isTreeOrd-tip item)
                   refl
          ⟩
        true && isTreeOrd (tip i) && ≤-TreeItem (tip item) i &&
        ≤-ItemTree i (tip i)
          ≡⟨ subst (λ t → true                    &&
                          isTreeOrd (tip i)       &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i)    ≡
                          true                    &&
                          t                       &&
                          ≤-TreeItem (tip item) i &&
                          ≤-ItemTree i (tip i))
                   (isTreeOrd-tip i)
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

    prf₂ : LE i item → TreeOrd (toTree ∙ item ∙ tip i)
    prf₂ i≤item =
      begin
        isTreeOrd (toTree ∙ item ∙ tip i)
          ≡⟨ subst (λ t → isTreeOrd (toTree ∙ item ∙ tip i) ≡ isTreeOrd t)
                   (toTree-tip item i)
                   refl
          ⟩
        isTreeOrd (if (i ≤ item)
                      then (node (tip i) item (tip item))
                      else (node (tip item) i (tip i)))
           ≡⟨ subst (λ t → isTreeOrd (if (i ≤ item)
                                         then (node (tip i) item (tip item))
                                         else (node (tip item) i (tip i))) ≡
                           isTreeOrd (if t
                                         then (node (tip i) item (tip item))
                                         else (node (tip item) i (tip i))))
                    (i≤item)
                    refl
           ⟩
        isTreeOrd (if true
                      then (node (tip i) item (tip item))
                      else (node (tip item) i (tip i)))
          ≡⟨ subst (λ t → isTreeOrd (if true
                                        then (node (tip i) item (tip item))
                                        else (node (tip item) i (tip i))) ≡
                                     isTreeOrd t)
                   (if-true (node (tip i) item (tip item)))
                   refl
          ⟩
        isTreeOrd (node (tip i) item (tip item))
          ≡⟨ isTreeOrd-node (tip i) item (tip item) ⟩
        isTreeOrd (tip i) && isTreeOrd (tip item) && ≤-TreeItem (tip i) item &&
        ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → isTreeOrd (tip i)           &&
                          isTreeOrd (tip item)        &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item)  ≡
                          t                           &&
                          isTreeOrd (tip item)        &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item))
                   (isTreeOrd-tip i)
                   refl
          ⟩
        true && isTreeOrd (tip item) && ≤-TreeItem (tip i) item &&
        ≤-ItemTree item (tip item)
          ≡⟨ subst (λ t → true                        &&
                          isTreeOrd (tip item)        &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item)  ≡
                          true                        &&
                          t                           &&
                          ≤-TreeItem (tip i) item     &&
                          ≤-ItemTree item (tip item))
                   (isTreeOrd-tip item)
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

toTree-TreeOrd {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) TOnodeT =
  [ prf₁ , prf₂ ] (x>y∨x≤y Ni Nitem)
  where
    prf₁ : GT i item → TreeOrd (toTree ∙ item ∙ node t₁ i t₂)
    prf₁ i>item =
      begin
        isTreeOrd (toTree ∙ item ∙ node t₁ i t₂)
          ≡⟨ subst (λ t → isTreeOrd (toTree ∙ item ∙ node t₁ i t₂) ≡
                          isTreeOrd t)
                   (toTree-node item t₁ i t₂)
                   refl
          ⟩
        isTreeOrd (if (i ≤ item)
                       then (node t₁ i (toTree ∙ item ∙ t₂))
                       else (node (toTree ∙ item ∙ t₁) i t₂))
           ≡⟨ subst (λ t → isTreeOrd (if (i ≤ item)
                                         then (node t₁ i (toTree ∙ item ∙ t₂))
                                         else (node (toTree ∙ item ∙ t₁) i t₂)) ≡
                           isTreeOrd (if t
                                         then (node t₁ i (toTree ∙ item ∙ t₂))
                                         else (node (toTree ∙ item ∙ t₁) i t₂)))
                    (x>y→x≰y Ni Nitem i>item)
                    refl
           ⟩
        isTreeOrd (if false
                      then (node t₁ i (toTree ∙ item ∙ t₂))
                      else (node (toTree ∙ item ∙ t₁) i t₂))
          ≡⟨ subst (λ t → isTreeOrd (if false
                                        then (node t₁ i (toTree ∙ item ∙ t₂))
                                        else (node (toTree ∙ item ∙ t₁) i t₂)) ≡
                                     isTreeOrd t)
                   (if-false (node (toTree ∙ item ∙ t₁) i t₂))
                   refl
          ⟩
        isTreeOrd (node (toTree ∙ item ∙ t₁) i t₂)
          ≡⟨ isTreeOrd-node (toTree ∙ item ∙ t₁) i t₂ ⟩
        isTreeOrd (toTree ∙ item ∙ t₁)    &&
        isTreeOrd t₂                      &&
        ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
        ≤-ItemTree i t₂
          ≡⟨ subst (λ t → isTreeOrd (toTree ∙ item ∙ t₁)    &&
                          isTreeOrd t₂                      &&
                          ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
                          ≤-ItemTree i t₂                   ≡
                          t                                 &&
                          isTreeOrd t₂                      &&
                          ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
                          ≤-ItemTree i t₂)
                   -- IH.
                   (toTree-TreeOrd Nitem Tt₁
                                   (leftSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT))
                   refl
          ⟩
        true && isTreeOrd t₂ && ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
        ≤-ItemTree i t₂
          ≡⟨ subst (λ t → true                              &&
                          isTreeOrd t₂                      &&
                          ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
                          ≤-ItemTree i t₂                   ≡
                          true                              &&
                          t                                 &&
                          ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
                          ≤-ItemTree i t₂)
                   (rightSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT)
                   refl
          ⟩
        true && true && ≤-TreeItem (toTree ∙ item ∙ t₁) i && ≤-ItemTree i t₂
          ≡⟨ subst (λ t → true                              &&
                          true                              &&
                          ≤-TreeItem (toTree ∙ item ∙ t₁) i &&
                          ≤-ItemTree i t₂                   ≡
                          true && true && t && ≤-ItemTree i t₂)
                   (toTree-TreeOrd-aux₁ Ni Nitem i>item Tt₁
                     ((w&&x&&y&&z≡true→y≡true
                        (isTreeOrd-Bool Tt₁)
                        (isTreeOrd-Bool Tt₂)
                        (≤-TreeItem-Bool Tt₁ Ni)
                        (≤-ItemTree-Bool Ni Tt₂)
                        (trans (sym (isTreeOrd-node t₁ i t₂)) TOnodeT))))
                   refl
          ⟩
        true && true && true && ≤-ItemTree i t₂
          ≡⟨ subst (λ t → true && true && true && ≤-ItemTree i t₂ ≡
                       true && true && true && t)
                   (w&&x&&y&&z≡true→z≡true
                     (isTreeOrd-Bool Tt₁)
                     (isTreeOrd-Bool Tt₂)
                     (≤-TreeItem-Bool Tt₁ Ni)
                     (≤-ItemTree-Bool Ni Tt₂)
                     (trans (sym (isTreeOrd-node t₁ i t₂)) TOnodeT))
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

    prf₂ : LE i item → TreeOrd (toTree ∙ item ∙ node t₁ i t₂)
    prf₂ i≤item =
      begin
        isTreeOrd (toTree ∙ item ∙ node t₁ i t₂)
          ≡⟨ subst (λ t → isTreeOrd (toTree ∙ item ∙ node t₁ i t₂) ≡
                          isTreeOrd t)
                   (toTree-node item t₁ i t₂)
                   refl
          ⟩
        isTreeOrd (if (i ≤ item)
                       then (node t₁ i (toTree ∙ item ∙ t₂))
                       else (node (toTree ∙ item ∙ t₁) i t₂))
           ≡⟨ subst (λ t → isTreeOrd (if (i ≤ item)
                                         then (node t₁ i (toTree ∙ item ∙ t₂))
                                         else (node (toTree ∙ item ∙ t₁) i t₂)) ≡
                           isTreeOrd (if t
                                         then (node t₁ i (toTree ∙ item ∙ t₂))
                                         else (node (toTree ∙ item ∙ t₁) i t₂)))
                    i≤item
                    refl
           ⟩
        isTreeOrd (if true
                      then (node t₁ i (toTree ∙ item ∙ t₂))
                      else (node (toTree ∙ item ∙ t₁) i t₂))
          ≡⟨ subst (λ t → isTreeOrd (if true
                                        then (node t₁ i (toTree ∙ item ∙ t₂))
                                        else (node (toTree ∙ item ∙ t₁) i t₂)) ≡
                                     isTreeOrd t)
                   (if-true (node t₁ i (toTree ∙ item ∙ t₂)))
                   refl
          ⟩
        isTreeOrd (node t₁ i (toTree ∙ item ∙ t₂))
          ≡⟨ isTreeOrd-node t₁ i (toTree ∙ item ∙ t₂) ⟩
        isTreeOrd t₁                   &&
        isTreeOrd (toTree ∙ item ∙ t₂) &&
        ≤-TreeItem t₁ i                &&
        ≤-ItemTree i (toTree ∙ item ∙ t₂)
          ≡⟨ subst (λ t → isTreeOrd t₁                      &&
                          isTreeOrd (toTree ∙ item ∙ t₂)    &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂) ≡
                          t                                 &&
                          isTreeOrd (toTree ∙ item ∙ t₂)    &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂))
                   (leftSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT)
                   refl
          ⟩
        true && isTreeOrd (toTree ∙ item ∙ t₂) && ≤-TreeItem t₁ i &&
        ≤-ItemTree i (toTree ∙ item ∙ t₂)
          ≡⟨ subst (λ t → true                              &&
                          isTreeOrd (toTree ∙ item ∙ t₂)    &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂) ≡
                          true                              &&
                          t                                 &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂))
                   -- IH.
                   (toTree-TreeOrd Nitem Tt₂
                     (rightSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT))
                   refl
          ⟩
        true && true && ≤-TreeItem t₁ i && ≤-ItemTree i (toTree ∙ item ∙ t₂)
          ≡⟨ subst (λ t → true                              &&
                          true                              &&
                          ≤-TreeItem t₁ i                   &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂) ≡
                          true                              &&
                          true                              &&
                          t                                 &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂))
                   (w&&x&&y&&z≡true→y≡true
                     (isTreeOrd-Bool Tt₁)
                     (isTreeOrd-Bool Tt₂)
                     (≤-TreeItem-Bool Tt₁ Ni)
                     (≤-ItemTree-Bool Ni Tt₂)
                     (trans (sym (isTreeOrd-node t₁ i t₂)) TOnodeT))
                   refl
          ⟩
        true && true && true && ≤-ItemTree i (toTree ∙ item ∙ t₂)
          ≡⟨ subst (λ t → true                              &&
                          true                              &&
                          true                              &&
                          ≤-ItemTree i (toTree ∙ item ∙ t₂) ≡
                          true && true && true && t)
                    (toTree-TreeOrd-aux₂ Ni Nitem i≤item Tt₂
                      ((w&&x&&y&&z≡true→z≡true
                        (isTreeOrd-Bool Tt₁)
                        (isTreeOrd-Bool Tt₂)
                        (≤-TreeItem-Bool Tt₁ Ni)
                        (≤-ItemTree-Bool Ni Tt₂)
                        (trans (sym (isTreeOrd-node t₁ i t₂)) TOnodeT))))
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
-- The function makeTree generates an ordered tree.
makeTree-TreeOrd : {is : D} → ListN is → TreeOrd (makeTree is)
makeTree-TreeOrd nilLN =
  begin
      isTreeOrd (foldr toTree nilTree [])
        ≡⟨ subst (λ t → isTreeOrd (foldr toTree nilTree []) ≡
                        isTreeOrd t)
                 (foldr-[] toTree nilTree)
                 refl
        ⟩
      isTreeOrd nilTree ≡⟨ isTreeOrd-nilTree ⟩
      true
      ∎

makeTree-TreeOrd (consLN {i} {is} Ni Lis) =
  begin
    isTreeOrd (foldr toTree nilTree (i ∷ is))
      ≡⟨ subst (λ t → isTreeOrd (foldr toTree nilTree (i ∷ is)) ≡
                      isTreeOrd t)
               (foldr-∷ toTree nilTree i is)
               refl
      ⟩
    isTreeOrd (toTree ∙ i ∙ (foldr toTree nilTree is))
      ≡⟨ toTree-TreeOrd Ni (makeTree-Tree Lis) (makeTree-TreeOrd Lis) ⟩
    true
  ∎
