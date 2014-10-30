------------------------------------------------------------------------------
-- Totality properties respect to OrdTree
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.SortList.Properties.Totality.OrdTreeATP where

open import FOTC.Base
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList
open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.Properties.Totality.TreeATP

------------------------------------------------------------------------------
-- Subtrees

-- If (node t₁ i t₂) is ordered then t₁ is ordered.
postulate leftSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                                OrdTree (node t₁ i t₂) → OrdTree t₁
{-# ATP prove leftSubTree-OrdTree &&-Bool &&-list₂-t le-ItemTree-Bool le-TreeItem-Bool ordTree-Bool #-}

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
postulate rightSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                                 OrdTree (node t₁ i t₂) → OrdTree t₂
{-# ATP prove rightSubTree-OrdTree &&-Bool &&-list₂-t le-ItemTree-Bool le-TreeItem-Bool ordTree-Bool #-}

------------------------------------------------------------------------------
-- Helper functions

toTree-OrdTree-helper₁ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → i₁ > i₂ →
                         Tree t →
                         ≤-TreeItem t i₁ →
                         ≤-TreeItem (toTree · i₂ · t) i₁
toTree-OrdTree-helper₁ {i₁} {i₂} .{nil} Ni₁ Ni₂ i₁>i₂ tnil t≤i₁ = prf
  where postulate prf : ≤-TreeItem (toTree · i₂ · nil) i₁
        {-# ATP prove prf x<y→x≤y #-}

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ (ttip {j} Nj) t≤i₁ =
  case prf₁ prf₂ (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : j > i₂ → ≤-TreeItem (toTree · i₂ · tip j) i₁
  {-# ATP prove prf₁ x>y→x≰y x<y→x≤y #-}

  postulate prf₂ : j ≤ i₂ → ≤-TreeItem (toTree · i₂ · tip j) i₁
  {-# ATP prove prf₂ x<y→x≤y #-}

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                       (tnode {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  case (prf₁ (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₁
               (&&-list₂-t₁ (le-TreeItem-Bool Tt₁ Ni₁)
                            (le-TreeItem-Bool Tt₂ Ni₁)
                            (trans (sym (le-TreeItem-node t₁ j t₂ i₁)) t≤i₁))))

       (prf₂ (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₂
               (&&-list₂-t₂ (le-TreeItem-Bool Tt₁ Ni₁)
                            (le-TreeItem-Bool Tt₂ Ni₁)
                            (trans (sym (le-TreeItem-node t₁ j t₂ i₁)) t≤i₁))))
       (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : ≤-TreeItem (toTree · i₂ · t₁) i₁ →
                   j > i₂ →
                   ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  {-# ATP prove prf₁ x>y→x≰y &&-list₂-t le-TreeItem-Bool #-}

  postulate prf₂ : ≤-TreeItem (toTree · i₂ · t₂) i₁ →
                   j ≤ i₂ →
                   ≤-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  {-# ATP prove prf₂ &&-list₂-t le-TreeItem-Bool #-}

toTree-OrdTree-helper₂ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → i₁ ≤ i₂ →
                         Tree t →
                         ≤-ItemTree i₁ t →
                         ≤-ItemTree i₁ (toTree · i₂ · t)
toTree-OrdTree-helper₂ {i₁} {i₂} .{nil} Ni₁ Ni₂ i₁≤i₂ tnil i₁≤t = prf
  where postulate prf : ≤-ItemTree i₁ (toTree · i₂ · nil)
        {-# ATP prove prf #-}

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (ttip {j} Nj) i₁≤t =
  case prf₁ prf₂ (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : j > i₂ → ≤-ItemTree i₁ (toTree · i₂ · tip j)
  {-# ATP prove prf₁ x>y→x≰y #-}

  postulate prf₂ : j ≤ i₂ → ≤-ItemTree i₁ (toTree · i₂ · tip j)
  {-# ATP prove prf₂ #-}

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                       (tnode {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  case (prf₁ (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
               (&&-list₂-t₁ (le-ItemTree-Bool Ni₁ Tt₁)
                            (le-ItemTree-Bool Ni₁ Tt₂)
                            (trans (sym (le-ItemTree-node i₁ t₁ j t₂)) i₁≤t))))

       (prf₂ (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
               (&&-list₂-t₂ (le-ItemTree-Bool Ni₁ Tt₁)
                            (le-ItemTree-Bool Ni₁ Tt₂)
                            (trans (sym (le-ItemTree-node i₁ t₁ j t₂)) i₁≤t))))
       (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : ≤-ItemTree i₁ (toTree · i₂ · t₁) →
                   j > i₂ →
                   ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  {-# ATP prove prf₁ x>y→x≰y &&-list₂-t le-ItemTree-Bool #-}

  postulate prf₂ : ≤-ItemTree i₁ (toTree · i₂ · t₂) →
                   j ≤ i₂ →
                   ≤-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  {-# ATP prove prf₂ &&-list₂-t le-ItemTree-Bool #-}
