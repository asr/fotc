------------------------------------------------------------------------------
-- Totality properties respect to OrdList (flatten-OrdList-helper)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdList.FlattenATP where

open import FOTC.Base
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.Properties.Totality.ListN-ATP
open import FOTC.Program.SortList.Properties.Totality.OrdTreeATP
open import FOTC.Program.SortList.Properties.MiscellaneousATP
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

flatten-OrdList-helper : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                         OrdTree (node t₁ i t₂) →
                         LE-Lists (flatten t₁) (flatten t₂)

flatten-OrdList-helper {t₂ = t₂} nilT Ni Tt₂ OTt =
  subst (λ t → LE-Lists t (flatten t₂))
        (sym (flatten-nilTree))
        (≤-Lists-[] (flatten t₂))

flatten-OrdList-helper (tipT {i₁} Ni₁) Tt₁ nilT OTt = prf
  where postulate prf : LE-Lists (flatten (tip i₁)) (flatten nilTree)
        {-# ATP prove prf #-}

flatten-OrdList-helper {i = i} (tipT {i₁} Ni₁) Ni (tipT {i₂} Ni₂) OTt = prf
  where
  postulate lemma : LE i₁ i₂
  {-# ATP prove lemma ≤-ItemTree-Bool ≤-TreeItem-Bool ordTree-Bool
                ≤-trans &&-list₄-t
  #-}

  postulate prf : LE-Lists (flatten (tip i₁)) (flatten (tip i₂))
  {-# ATP prove prf lemma #-}

flatten-OrdList-helper {i = i} (tipT {i₁} Ni₁) Ni
                       (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt = prf
  where
  -- Helper terms to get the conjuncts from OTt.
  helper₁ = ordTree-Bool (tipT Ni₁)
  helper₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
  helper₃ = ≤-TreeItem-Bool (tipT Ni₁) Ni
  helper₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
  helper₅ = trans (sym (ordTree-node (tip i₁) i (node t₂₁ i₂ t₂₂))) OTt

  -- Helper terms to get the conjuncts from the fourth conjunct of OTt
  helper₆ = ≤-ItemTree-Bool Ni Tt₂₁
  helper₇ = ≤-ItemTree-Bool Ni Tt₂₂
  helper₈ = trans (sym (≤-ItemTree-node i t₂₁ i₂ t₂₂))
                  (&&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅)

  -- Common terms for the lemma₁ and lemma₂.
  -- The ATPs could not figure out them.
  OrdTree-tip-i₁ : OrdTree (tip i₁)
  OrdTree-tip-i₁ = &&-list₄-t₁ helper₁ helper₂ helper₃ helper₄ helper₅

  LE-TreeItem-tip-i₁-i : LE-TreeItem (tip i₁) i
  LE-TreeItem-tip-i₁-i = &&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅

  lemma₁ : LE-Lists (flatten (tip i₁)) (flatten t₂₁)
  lemma₁ = flatten-OrdList-helper (tipT Ni₁) Ni Tt₂₁ OT
    where
    -- The ATPs could not figure these terms.
    OrdTree-t₂₁ : OrdTree t₂₁
    OrdTree-t₂₁ =
      leftSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                          (&&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅)

    LE-ItemTree-i-t₂₁ : LE-ItemTree i t₂₁
    LE-ItemTree-i-t₂₁ = &&-list₂-t₁ helper₆ helper₇ helper₈

    postulate OT : OrdTree (node (tip i₁) i t₂₁)
    {-# ATP prove OT OrdTree-tip-i₁
                     OrdTree-t₂₁
                     LE-TreeItem-tip-i₁-i
                     LE-ItemTree-i-t₂₁
    #-}

  lemma₂ : LE-Lists (flatten (tip i₁)) (flatten t₂₂)
  lemma₂ = flatten-OrdList-helper (tipT Ni₁) Ni Tt₂₂ OT
    where
    -- The ATPs could not figure these terms.
    OrdTree-t₂₂ : OrdTree t₂₂
    OrdTree-t₂₂ =
      rightSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                           (&&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅)

    LE-ItemTree-i-t₂₂ : LE-ItemTree i t₂₂
    LE-ItemTree-i-t₂₂ = &&-list₂-t₂ helper₆ helper₇ helper₈

    postulate OT : OrdTree (node (tip i₁) i t₂₂)
    {-# ATP prove OT OrdTree-tip-i₁
                     OrdTree-t₂₂
                     LE-TreeItem-tip-i₁-i
                     LE-ItemTree-i-t₂₂
    #-}

  postulate prf : LE-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂))
  {-# ATP prove prf xs≤ys→xs≤zs→xs≤ys++zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-helper {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂)
                       Ni nilT OTt = prf
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

  lemma₁ : LE-Lists (flatten t₁₁) (flatten nilTree)
  lemma₁ = flatten-OrdList-helper Tt₁₁ Ni nilT OT
    where
    postulate OT : OrdTree (node t₁₁ i nilTree)
    {-# ATP prove OT leftSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  lemma₂ : LE-Lists (flatten t₁₂) (flatten nilTree)
  lemma₂ = flatten-OrdList-helper Tt₁₂ Ni nilT OT
    where
    postulate OT : OrdTree (node t₁₂ i nilTree)
    {-# ATP prove OT rightSubTree-OrdTree
                     &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  postulate prf : LE-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nilTree)
  {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-helper {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (tipT {i₂} Ni₂) OTt = prf
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

  lemma₁ : LE-Lists (flatten t₁₁) (flatten (tip i₂))
  lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (tipT Ni₂) OT
    where
    postulate OT : OrdTree (node t₁₁ i (tip i₂))
    {-# ATP prove OT leftSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  lemma₂ : LE-Lists (flatten t₁₂) (flatten (tip i₂))
  lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (tipT Ni₂) OT
    where
    postulate OT : OrdTree (node t₁₂ i (tip i₂))
    {-# ATP prove OT rightSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  postulate prf : LE-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂))
  {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-helper {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt = prf
  where
  -- Helper terms to get the conjuncts from OTt.
  helper₁ = ordTree-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂)
  helper₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
  helper₃ = ≤-TreeItem-Bool (nodeT Tt₁₁ Ni₁ Tt₁₂) Ni
  helper₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
  helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (node t₂₁ i₂ t₂₂)))
                    OTt

  -- Helper terms to get the conjuncts from the third conjunct of OTt.
  helper₆ = ≤-TreeItem-Bool Tt₁₁ Ni
  helper₇ = ≤-TreeItem-Bool Tt₁₂ Ni
  helper₈ = trans (sym (≤-TreeItem-node t₁₁ i₁ t₁₂ i))
                  (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

  lemma₁ : LE-Lists (flatten t₁₁) (flatten (node t₂₁ i₂ t₂₂))
  lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT
    where
    postulate OT : OrdTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
    {-# ATP prove OT leftSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  lemma₂ : LE-Lists (flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
  lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT
    where
    postulate OT : OrdTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
    {-# ATP prove OT rightSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  postulate prf : LE-Lists (flatten (node t₁₁ i₁ t₁₂))
                  (flatten (node t₂₁ i₂ t₂₂))
  {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}
