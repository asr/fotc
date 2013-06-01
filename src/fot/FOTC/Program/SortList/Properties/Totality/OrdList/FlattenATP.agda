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
                         ≤-Lists (flatten t₁) (flatten t₂)

flatten-OrdList-helper {t₂ = t₂} tnil Ni Tt₂ OTt =
  subst (λ t → ≤-Lists t (flatten t₂))
        (sym (flatten-nil))
        (le-Lists-[] (flatten t₂))

flatten-OrdList-helper (ttip {i₁} Ni₁) Tt₁ tnil OTt = prf
  where postulate prf : ≤-Lists (flatten (tip i₁)) (flatten nil)
        {-# ATP prove prf #-}

flatten-OrdList-helper {i = i} (ttip {i₁} Ni₁) Ni (ttip {i₂} Ni₂) OTt = prf
  where
  postulate lemma : i₁ ≤ i₂
  {-# ATP prove lemma ≤-trans &&-list₄-t
                      le-ItemTree-Bool le-TreeItem-Bool ordTree-Bool
  #-}

  postulate prf : ≤-Lists (flatten (tip i₁)) (flatten (tip i₂))
  {-# ATP prove prf lemma #-}

flatten-OrdList-helper {i = i} (ttip {i₁} Ni₁) Ni
                       (tnode {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt = prf
  where
  -- Helper terms to get the conjuncts from OTt.
  helper₁ = ordTree-Bool (ttip Ni₁)
  helper₂ = ordTree-Bool (tnode Tt₂₁ Ni₂ Tt₂₂)
  helper₃ = le-TreeItem-Bool (ttip Ni₁) Ni
  helper₄ = le-ItemTree-Bool Ni (tnode Tt₂₁ Ni₂ Tt₂₂)
  helper₅ = trans (sym (ordTree-node (tip i₁) i (node t₂₁ i₂ t₂₂))) OTt

  -- Helper terms to get the conjuncts from the fourth conjunct of OTt
  helper₆ = le-ItemTree-Bool Ni Tt₂₁
  helper₇ = le-ItemTree-Bool Ni Tt₂₂
  helper₈ = trans (sym (le-ItemTree-node i t₂₁ i₂ t₂₂))
                  (&&-list₄-t₄ helper₁ helper₂ helper₃ helper₄ helper₅)

  -- Common terms for the lemma₁ and lemma₂.
  -- The ATPs could not figure out them.
  OrdTree-tip-i₁ : OrdTree (tip i₁)
  OrdTree-tip-i₁ = &&-list₄-t₁ helper₁ helper₂ helper₃ helper₄ helper₅

  ≤-TreeItem-tip-i₁-i : ≤-TreeItem (tip i₁) i
  ≤-TreeItem-tip-i₁-i = &&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅

  lemma₁ : ≤-Lists (flatten (tip i₁)) (flatten t₂₁)
  lemma₁ = flatten-OrdList-helper (ttip Ni₁) Ni Tt₂₁ OT
    where
    -- The ATPs could not figure these terms.
    OrdTree-t₂₁ : OrdTree t₂₁
    OrdTree-t₂₁ =
      leftSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                          (&&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅)

    ≤-ItemTree-i-t₂₁ : ≤-ItemTree i t₂₁
    ≤-ItemTree-i-t₂₁ = &&-list₂-t₁ helper₆ helper₇ helper₈

    postulate OT : OrdTree (node (tip i₁) i t₂₁)
    {-# ATP prove OT ≤-TreeItem-tip-i₁-i
                     ≤-ItemTree-i-t₂₁
                     OrdTree-tip-i₁
                     OrdTree-t₂₁
    #-}

  lemma₂ : ≤-Lists (flatten (tip i₁)) (flatten t₂₂)
  lemma₂ = flatten-OrdList-helper (ttip Ni₁) Ni Tt₂₂ OT
    where
    -- The ATPs could not figure these terms.
    OrdTree-t₂₂ : OrdTree t₂₂
    OrdTree-t₂₂ =
      rightSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                           (&&-list₄-t₂ helper₁ helper₂ helper₃ helper₄ helper₅)

    ≤-ItemTree-i-t₂₂ : ≤-ItemTree i t₂₂
    ≤-ItemTree-i-t₂₂ = &&-list₂-t₂ helper₆ helper₇ helper₈

    postulate OT : OrdTree (node (tip i₁) i t₂₂)
    {-# ATP prove OT ≤-TreeItem-tip-i₁-i
                     ≤-ItemTree-i-t₂₂
                     OrdTree-tip-i₁
                     OrdTree-t₂₂
    #-}

  postulate prf : ≤-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂))
  {-# ATP prove prf xs≤ys→xs≤zs→xs≤ys++zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-helper {i = i} (tnode {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂)
                       Ni tnil OTt = prf
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

  lemma₁ : ≤-Lists (flatten t₁₁) (flatten nil)
  lemma₁ = flatten-OrdList-helper Tt₁₁ Ni tnil OT
    where
    postulate OT : OrdTree (node t₁₁ i nil)
    {-# ATP prove OT leftSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  lemma₂ : ≤-Lists (flatten t₁₂) (flatten nil)
  lemma₂ = flatten-OrdList-helper Tt₁₂ Ni tnil OT
    where
    postulate OT : OrdTree (node t₁₂ i nil)
    {-# ATP prove OT rightSubTree-OrdTree
                     &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  postulate prf : ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nil)
  {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-helper {i = i} (tnode {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (ttip {i₂} Ni₂) OTt = prf
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

  lemma₁ : ≤-Lists (flatten t₁₁) (flatten (tip i₂))
  lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (ttip Ni₂) OT
    where
    postulate OT : OrdTree (node t₁₁ i (tip i₂))
    {-# ATP prove OT leftSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  lemma₂ : ≤-Lists (flatten t₁₂) (flatten (tip i₂))
  lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (ttip Ni₂) OT
    where
    postulate OT : OrdTree (node t₁₂ i (tip i₂))
    {-# ATP prove OT rightSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  postulate prf : ≤-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂))
  {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-helper {i = i} (tnode {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                       (tnode {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt = prf
  where
  -- Helper terms to get the conjuncts from OTt.
  helper₁ = ordTree-Bool (tnode Tt₁₁ Ni₁ Tt₁₂)
  helper₂ = ordTree-Bool (tnode Tt₂₁ Ni₂ Tt₂₂)
  helper₃ = le-TreeItem-Bool (tnode Tt₁₁ Ni₁ Tt₁₂) Ni
  helper₄ = le-ItemTree-Bool Ni (tnode Tt₂₁ Ni₂ Tt₂₂)
  helper₅ = trans (sym (ordTree-node (node t₁₁ i₁ t₁₂) i (node t₂₁ i₂ t₂₂)))
                    OTt

  -- Helper terms to get the conjuncts from the third conjunct of OTt.
  helper₆ = le-TreeItem-Bool Tt₁₁ Ni
  helper₇ = le-TreeItem-Bool Tt₁₂ Ni
  helper₈ = trans (sym (le-TreeItem-node t₁₁ i₁ t₁₂ i))
                  (&&-list₄-t₃ helper₁ helper₂ helper₃ helper₄ helper₅)

  lemma₁ : ≤-Lists (flatten t₁₁) (flatten (node t₂₁ i₂ t₂₂))
  lemma₁ = flatten-OrdList-helper Tt₁₁ Ni (tnode Tt₂₁ Ni₂ Tt₂₂) OT
    where
    postulate OT : OrdTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
    {-# ATP prove OT leftSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  lemma₂ : ≤-Lists (flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
  lemma₂ = flatten-OrdList-helper Tt₁₂ Ni (tnode Tt₂₁ Ni₂ Tt₂₂) OT
    where
    postulate OT : OrdTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
    {-# ATP prove OT rightSubTree-OrdTree
                     &&-list₂-t &&-list₄-t
                     helper₁ helper₂ helper₃ helper₄ helper₅ helper₆
                     helper₇ helper₈
    #-}

  postulate prf : ≤-Lists (flatten (node t₁₁ i₁ t₁₂))
                  (flatten (node t₂₁ i₂ t₂₂))
  {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}
