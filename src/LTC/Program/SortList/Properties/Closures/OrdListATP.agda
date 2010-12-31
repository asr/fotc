------------------------------------------------------------------------------
-- Closures properties respect to OrdList
------------------------------------------------------------------------------

module LTC.Program.SortList.Properties.Closures.OrdListATP where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Bool.PropertiesATP
  using ( ≤-Bool
        ; &&-proj₁
        ; &&-proj₂
        ; &&₃-proj₁
        ; &&₃-proj₂
        ; &&₃-proj₃
        ; &&₃-proj₄
        )
open import LTC.Data.Nat.Inequalities using ( LE )
open import LTC.Data.Nat.Inequalities.PropertiesATP using ( ≤-trans )

open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )
open import LTC.Data.List using ( _++_ ; ++-[] )

open import LTC.Program.SortList.Properties.Closures.BoolATP
  using ( ≤-ItemList-Bool
        ; ≤-ItemTree-Bool
        ; ≤-Lists-Bool
        ; ≤-TreeItem-Bool
        ; ordList-Bool
        ; ordTree-Bool
        )
open import LTC.Program.SortList.Properties.Closures.ListATP
  using ( flatten-List )
open import LTC.Program.SortList.Properties.Closures.OrdTreeATP
  using ( leftSubTree-OrdTree
        ; rightSubTree-OrdTree
        )
open import LTC.Program.SortList.Properties.MiscellaneousATP
  using ( xs≤zs→ys≤zs→xs++ys≤zs
        ; xs≤ys→xs≤zs→xs≤ys++zs
        )
open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- If (i ∷ is) is ordered then 'is' is ordered.
subList-OrdList : {i : D} → N i → {is : D} → ListN is → OrdList (i ∷ is) →
                  OrdList is
subList-OrdList {i} Ni nilLN LOi∷is = ordList-[]

subList-OrdList {i} Ni (consLN {j} {js} Nj Ljs) LOi∷j∷js = prf
  where
    postulate prf : OrdList (j ∷ js)
    -- E 1.2: Non-tested.
    -- Equinox 5.0alpha (2010-06-29): Non-tested.
    -- Metis 2.3 : Non-tested.
    {-# ATP prove prf &&-proj₂ ≤-ItemList-Bool ordList-Bool #-}

------------------------------------------------------------------------------
-- Auxiliar functions
++-OrdList-aux : {item is js : D} → N item → ListN is → ListN js →
                 LE-ItemList item is →
                 LE-ItemList item js →
                 LE-Lists is js →
                 LE-ItemList item (is ++ js)

++-OrdList-aux {item} {js = js} _ nilLN _ _ item≤js _ =
  subst (λ t → LE-ItemList item t) (sym (++-[] js)) item≤js

++-OrdList-aux {item} {js = js} Nitem
               (consLN {i} {is} Ni LNis) LNjs item≤i∷is item≤js i∷is≤js =
  prf (++-OrdList-aux Nitem LNis LNjs lemma₁ item≤js lemma₂)
  where
    lemma₁ : ≤-ItemList item is ≡ true
    lemma₁ =  &&-proj₂ (≤-Bool Nitem Ni)
                       (≤-ItemList-Bool Nitem LNis)
                       (trans (sym $ ≤-ItemList-∷ item i is) item≤i∷is)

    lemma₂ : ≤-Lists is js ≡ true
    lemma₂ = &&-proj₂ (≤-ItemList-Bool Ni LNjs)
                      (≤-Lists-Bool LNis LNjs)
                      (trans (sym $ ≤-Lists-∷ i is js) i∷is≤js)

    postulate prf : LE-ItemList item (is ++ js) →  -- IH.
                    LE-ItemList item ((i ∷ is) ++ js)
    -- E 1.2: Non-tested.
    -- Metis 2.3 : Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf ≤-Bool ≤-ItemList-Bool &&-proj₁ #-}

flatten-OrdList-aux : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ →
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

flatten-OrdList-aux {i = i} (tipT {i1} Ni1) Ni
                    (nodeT {t21} {i2} {t22} Tt21 Ni2 Tt22) OTt = prf
  where
    -- Auxiliary terms to get the conjuncts from OTt.
    aux₁ = ordTree-Bool (tipT Ni1)
    aux₂ = ordTree-Bool (nodeT Tt21 Ni2 Tt22)
    aux₃ = ≤-TreeItem-Bool (tipT Ni1) Ni
    aux₄ = ≤-ItemTree-Bool Ni (nodeT Tt21 Ni2 Tt22)
    aux₅ = trans (sym (ordTree-node (tip i1) i (node t21 i2 t22))) OTt

    -- Auxiliary terms to get the conjuncts from the fourth conjunct of OTt
    aux₆ = ≤-ItemTree-Bool Ni Tt21
    aux₇ = ≤-ItemTree-Bool Ni Tt22
    aux₈ = trans (sym (≤-ItemTree-node i t21 i2 t22))
                 (&&₃-proj₄ aux₁ aux₂ aux₃ aux₄ aux₅)

    -- Common terms for the lemma₁ and lemma₂.
    -- The ATPs could not figure out them.
    OrdTree-tip-i1 : OrdTree (tip i1)
    OrdTree-tip-i1 = &&₃-proj₁ aux₁ aux₂ aux₃ aux₄ aux₅

    LE-TreeItem-tip-i1-i : LE-TreeItem (tip i1) i
    LE-TreeItem-tip-i1-i = &&₃-proj₃ aux₁ aux₂ aux₃ aux₄ aux₅

    lemma₁ : LE-Lists (flatten (tip i1)) (flatten t21)
    lemma₁ = flatten-OrdList-aux (tipT Ni1) Ni Tt21 OT  -- IH.
      where
        -- The ATPs could not figure these terms.
        OrdTree-t21 : OrdTree t21
        OrdTree-t21 = leftSubTree-OrdTree Tt21 Ni2 Tt22
                                          (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t21 : LE-ItemTree i t21
        LE-ItemTree-i-t21 = &&-proj₁ aux₆ aux₇ aux₈

        postulate OT : OrdTree (node (tip i1) i t21)
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT OrdTree-tip-i1
                         OrdTree-t21
                         LE-TreeItem-tip-i1-i
                         LE-ItemTree-i-t21
        #-}

    lemma₂ : LE-Lists (flatten (tip i1)) (flatten t22)
    lemma₂ = flatten-OrdList-aux (tipT Ni1) Ni Tt22 OT  -- IH.
      where
        -- The ATPs could not figure these terms.
        OrdTree-t22 : OrdTree t22
        OrdTree-t22 = rightSubTree-OrdTree Tt21 Ni2 Tt22
                                           (&&₃-proj₂ aux₁ aux₂ aux₃ aux₄ aux₅)

        LE-ItemTree-i-t22 : LE-ItemTree i t22
        LE-ItemTree-i-t22 = &&-proj₂ aux₆ aux₇ aux₈

        postulate OT : OrdTree (node (tip i1) i t22)
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT OrdTree-tip-i1
                         OrdTree-t22
                         LE-TreeItem-tip-i1-i
                         LE-ItemTree-i-t22
        #-}

    postulate prf : LE-Lists (flatten (tip i1)) (flatten (node t21 i2 t22))
    -- E 1.2: Non-tested.
    -- Metis 2.3 : Non-tested.
    -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf xs≤ys→xs≤zs→xs≤ys++zs flatten-List lemma₁ lemma₂ #-}

flatten-OrdList-aux {i = i} (nodeT {t11} {i1} {t12} Tt11 Ni1 Tt12)
                    Ni nilT OTt = prf
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

    lemma₁ : LE-Lists (flatten t11) (flatten nilTree)
    lemma₁ = flatten-OrdList-aux Tt11 Ni nilT OT  -- IH.
      where
        postulate OT : OrdTree (node t11 i nilTree)
        -- E 1.2: Non-tested.
        -- Equinox 5.0alpha (2010-06-29): Non-tested.
        -- Metis 2.3 : Non-tested.
        {-# ATP prove OT leftSubTree-OrdTree
                         &&₃-proj₁ &&-proj₁ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    lemma₂ : LE-Lists (flatten t12) (flatten nilTree)
    lemma₂ = flatten-OrdList-aux Tt12 Ni nilT OT
      where
        postulate OT : OrdTree (node t12 i nilTree)
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT rightSubTree-OrdTree
                         &&₃-proj₁ &&₃-proj₂ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    postulate prf : LE-Lists (flatten (node t11 i1 t12)) (flatten nilTree)
      -- E 1.2: Non-tested.
      -- Equinox 5.0alpha (2010-06-29): Non-tested.
      -- Metis 2.3 : Non-tested.
    {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-List lemma₁ lemma₂ #-}

flatten-OrdList-aux {i = i} (nodeT {t11} {i1} {t12} Tt11 Ni1 Tt12) Ni
                    (tipT {i2} Ni2) OTt = prf
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

    lemma₁ : LE-Lists (flatten t11) (flatten (tip i2))
    lemma₁ = flatten-OrdList-aux Tt11 Ni (tipT Ni2) OT  -- IH.
      where
        postulate OT : OrdTree (node t11 i (tip i2))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT leftSubTree-OrdTree
                         &&₃-proj₁ &&₃-proj₂ &&-proj₁ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    lemma₂ : LE-Lists (flatten t12) (flatten (tip i2))
    lemma₂ = flatten-OrdList-aux Tt12 Ni (tipT Ni2) OT  -- IH.
      where
        postulate OT : OrdTree (node t12 i (tip i2))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT rightSubTree-OrdTree
                         &&-proj₂ &&₃-proj₁ &&₃-proj₂ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈ #-}

    postulate prf : LE-Lists (flatten (node t11 i1 t12)) (flatten (tip i2))
      -- E 1.2: Non-tested.
      -- Metis 2.3 : Non-tested.
      -- Vampire 0.6 (revision 903): Non-tested.
    {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-List lemma₁ lemma₂ #-}

flatten-OrdList-aux {i = i} (nodeT {t11} {i1} {t12} Tt11 Ni1 Tt12) Ni
                    (nodeT {t21} {i2} {t22} Tt21 Ni2 Tt22) OTt = prf

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

    lemma₁ : LE-Lists (flatten t11) (flatten (node t21 i2 t22))
    lemma₁ = flatten-OrdList-aux Tt11 Ni (nodeT Tt21 Ni2 Tt22) OT  -- IH.
      where
        postulate OT : OrdTree (node t11 i (node t21 i2 t22))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT leftSubTree-OrdTree
                         &&₃-proj₁ &&₃-proj₂ &&-proj₁ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈
        #-}

    lemma₂ : LE-Lists (flatten t12) (flatten (node t21 i2 t22))
    lemma₂ = flatten-OrdList-aux Tt12 Ni (nodeT Tt21 Ni2 Tt22) OT  -- IH.
      where
        postulate OT : OrdTree (node t12 i (node t21 i2 t22))
        -- E 1.2: Non-tested.
        -- Metis 2.3 : Non-tested.
        -- Vampire 0.6 (revision 903): Non-tested.
        {-# ATP prove OT rightSubTree-OrdTree
                         &&-proj₂ &&₃-proj₁ &&₃-proj₂ &&₃-proj₄
                         aux₁ aux₂ aux₃ aux₄ aux₅ aux₆ aux₇ aux₈ #-}

    postulate prf : LE-Lists (flatten (node t11 i1 t12)) (flatten (node t21 i2 t22))
      -- E 1.2: Non-tested.
      -- Metis 2.3 : Non-tested.
      -- Equinox 5.0alpha (2010-06-29): Non-tested.
    {-# ATP prove prf xs≤zs→ys≤zs→xs++ys≤zs flatten-List lemma₁ lemma₂ #-}
