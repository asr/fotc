------------------------------------------------------------------------------
-- Closures properties respect to OrdList (flatten-OrdList-aux)
------------------------------------------------------------------------------

module LTC.Program.SortList.Properties.Closures.OrdList.FlattenATP where

open import LTC.Base

open import LTC.Data.Bool.PropertiesATP
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.Type

open import LTC.Program.SortList.Properties.Closures.BoolATP
open import LTC.Program.SortList.Properties.Closures.ListN-ATP
open import LTC.Program.SortList.Properties.Closures.OrdTreeATP
open import LTC.Program.SortList.Properties.MiscellaneousATP
open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------

flatten-OrdList-aux : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                      OrdTree (node t₁ i t₂) →
                      LE-Lists (flatten t₁) (flatten t₂)

flatten-OrdList-aux {t₂ = t₂} nilT Ni Tt₂ OTt =
  subst (λ t → LE-Lists t (flatten t₂))
        (sym (flatten-nilTree))
        (≤-Lists-[] (flatten t₂))

flatten-OrdList-aux (tipT {i₁} Ni₁) _ nilT OTt = prf
  where
    postulate prf : LE-Lists (flatten (tip i₁)) (flatten nilTree)
    -- Equinox 5.0alpha (2010-06-29): Non-tested.
    -- Metis 2.3 : Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf #-}

flatten-OrdList-aux {i = i} (tipT {i₁} Ni₁) Ni (tipT {i₂} Ni₂) OTt = prf
  where
    postulate lemma : LE i₁ i₂
    -- E 1.2: Non-tested.
    -- Equinox 5.0alpha (2010-06-29): Non-tested.
    -- Metis 2.3 : Non-tested.
    {-# ATP prove lemma ≤-ItemTree-Bool ≤-TreeItem-Bool ordTree-Bool
                  ≤-trans &&₃-proj₃ &&₃-proj₄
    #-}

    postulate prf : LE-Lists (flatten (tip i₁)) (flatten (tip i₂))
    -- Equinox 5.0alpha (2010-06-29): Non-tested.
    -- Metis 2.3 : Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf lemma #-}

flatten-OrdList-aux {i = i} (tipT {i₁} Ni₁) Ni
                    (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt = prf
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (tipT Ni₁)
    aux₂ = ordTree-Bool (nodeT Tt₂₁ Ni₂ Tt₂₂)
    aux₃ = ≤-TreeItem-Bool (tipT Ni₁) Ni
    aux₄ = ≤-ItemTree-Bool Ni (nodeT Tt₂₁ Ni₂ Tt₂₂)
    aux₅ = trans (sym (ordTree-node (tip i₁) i (node t₂₁ i₂ t₂₂))) OTt

    -- Auxiliary terms to get the conjuncts from the fourth conjunct of OTt
    aux₆ = ≤-ItemTree-Bool Ni Tt₂₁
    aux₇ = ≤-ItemTree-Bool Ni Tt₂₂
    aux₈ = trans (sym (≤-ItemTree-node i t₂₁ i₂ t₂₂))
                 (&&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    -- The ATPs could not figure out them.
    OrdTree-tip-i₁ : OrdTree (tip i₁)
    OrdTree-tip-i₁ = &&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-TreeItem-tip-i₁-i : LE-TreeItem (tip i₁) i
    LE-TreeItem-tip-i₁-i = &&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten (tip i₁)) (flatten t₂₁)
    lemma₁ = flatten-OrdList-aux (tipT Ni₁) Ni Tt₂₁ OT  -- IH.
      where
        -- The ATPs could not figure these terms.
        OrdTree-t₂₁ : OrdTree t₂₁
        OrdTree-t₂₁ = leftSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                                          (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t₂₁ : LE-ItemTree i t₂₁
        LE-ItemTree-i-t₂₁ = &&-proj₁ aux₆ aux₇ aux₈

        postulate OT : OrdTree (node (tip i₁) i t₂₁)
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT OrdTree-tip-i₁
                         OrdTree-t₂₁
                         LE-TreeItem-tip-i₁-i
                         LE-ItemTree-i-t₂₁
        #-}

    lemma₂ : LE-Lists (flatten (tip i₁)) (flatten t₂₂)
    lemma₂ = flatten-OrdList-aux (tipT Ni₁) Ni Tt₂₂ OT  -- IH.
      where
        -- The ATPs could not figure these terms.
        OrdTree-t₂₂ : OrdTree t₂₂
        OrdTree-t₂₂ = rightSubTree-OrdTree Tt₂₁ Ni₂ Tt₂₂
                                           (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t₂₂ : LE-ItemTree i t₂₂
        LE-ItemTree-i-t₂₂ = &&-proj₂ aux₆ aux₇ aux₈

        postulate OT : OrdTree (node (tip i₁) i t₂₂)
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT OrdTree-tip-i₁
                         OrdTree-t₂₂
                         LE-TreeItem-tip-i₁-i
                         LE-ItemTree-i-t₂₂
        #-}

    postulate prf : LE-Lists (flatten (tip i₁)) (flatten (node t₂₁ i₂ t₂₂))
    -- E 1.2: Non-tested.
    -- Metis 2.3 : Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf xs≤ys→xs≤zs→xs≤ys++zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-aux {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂)
                    Ni nilT OTt = prf
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

    lemma₁ : LE-Lists (flatten t₁₁) (flatten nilTree)
    lemma₁ = flatten-OrdList-aux Tt₁₁ Ni nilT OT  -- IH.
      where
        postulate OT : OrdTree (node t₁₁ i nilTree)
        -- E 1.2: Non-tested.
        -- Equinox 5.0alpha (2010-06-29): Non-tested.
        -- Metis 2.3 : Non-tested.
        {-# ATP prove OT leftSubTree-OrdTree
                         &&₃-proj₁ &&-proj₁ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    lemma₂ : LE-Lists (flatten t₁₂) (flatten nilTree)
    lemma₂ = flatten-OrdList-aux Tt₁₂ Ni nilT OT
      where
        postulate OT : OrdTree (node t₁₂ i nilTree)
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT rightSubTree-OrdTree
                         &&₃-proj₁ &&₃-proj₂ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    postulate prf : LE-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten nilTree)
      -- E 1.2: Non-tested.
      -- Equinox 5.0alpha (2010-06-29): Non-tested.
      -- Metis 2.3 : Non-tested.
    {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-aux {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                    (tipT {i₂} Ni₂) OTt = prf
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

    lemma₁ : LE-Lists (flatten t₁₁) (flatten (tip i₂))
    lemma₁ = flatten-OrdList-aux Tt₁₁ Ni (tipT Ni₂) OT  -- IH.
      where
        postulate OT : OrdTree (node t₁₁ i (tip i₂))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT leftSubTree-OrdTree
                         &&₃-proj₁ &&₃-proj₂ &&-proj₁ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    lemma₂ : LE-Lists (flatten t₁₂) (flatten (tip i₂))
    lemma₂ = flatten-OrdList-aux Tt₁₂ Ni (tipT Ni₂) OT  -- IH.
      where
        postulate OT : OrdTree (node t₁₂ i (tip i₂))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT rightSubTree-OrdTree
                         &&-proj₂ &&₃-proj₁ &&₃-proj₂ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈ #-}

    postulate prf : LE-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (tip i₂))
      -- E 1.2: Non-tested.
      -- Metis 2.3 : Non-tested.
      -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}

flatten-OrdList-aux {i = i} (nodeT {t₁₁} {i₁} {t₁₂} Tt₁₁ Ni₁ Tt₁₂) Ni
                    (nodeT {t₂₁} {i₂} {t₂₂} Tt₂₁ Ni₂ Tt₂₂) OTt = prf

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

    lemma₁ : LE-Lists (flatten t₁₁) (flatten (node t₂₁ i₂ t₂₂))
    lemma₁ = flatten-OrdList-aux Tt₁₁ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT  -- IH.
      where
        postulate OT : OrdTree (node t₁₁ i (node t₂₁ i₂ t₂₂))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT leftSubTree-OrdTree
                         &&₃-proj₁ &&₃-proj₂ &&-proj₁ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    lemma₂ : LE-Lists (flatten t₁₂) (flatten (node t₂₁ i₂ t₂₂))
    lemma₂ = flatten-OrdList-aux Tt₁₂ Ni (nodeT Tt₂₁ Ni₂ Tt₂₂) OT  -- IH.
      where
        postulate OT : OrdTree (node t₁₂ i (node t₂₁ i₂ t₂₂))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT rightSubTree-OrdTree
                         &&-proj₂ &&₃-proj₁ &&₃-proj₂ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈ #-}

    postulate prf : LE-Lists (flatten (node t₁₁ i₁ t₁₂)) (flatten (node t₂₁ i₂ t₂₂))
      -- E 1.2: Non-tested.
      -- Metis 2.3 : Non-tested.
      -- Equinox 5.0alpha (2010-06-29): Non-tested.
    {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-ListN lemma₁ lemma₂ #-}
