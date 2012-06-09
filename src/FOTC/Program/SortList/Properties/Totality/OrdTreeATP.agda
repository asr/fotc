------------------------------------------------------------------------------
-- Totality properties respect to OrdTree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.OrdTreeATP where

open import Common.Function

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
-- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
postulate
  leftSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                        OrdTree (node t₁ i t₂) → OrdTree t₁
{-# ATP prove leftSubTree-OrdTree ≤-ItemTree-Bool ≤-TreeItem-Bool &&-Bool
                                  ordTree-Bool &&-list₂-true
#-}

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
-- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
postulate
  rightSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                         OrdTree (node t₁ i t₂) → OrdTree t₂
{-# ATP prove rightSubTree-OrdTree ≤-ItemTree-Bool ≤-TreeItem-Bool &&-Bool
                                   ordTree-Bool &&-list₂-true
#-}

------------------------------------------------------------------------------
-- Helper functions

toTree-OrdTree-helper₁ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → GT i₁ i₂ →
                         Tree t →
                         LE-TreeItem t i₁ →
                         LE-TreeItem (toTree · i₂ · t) i₁
toTree-OrdTree-helper₁ {i₁} {i₂} .{nilTree} Ni₁ Ni₂ i₁>i₂ nilT t≤i₁ = prf
  where
  postulate prf : LE-TreeItem (toTree · i₂ · nilTree) i₁
  {-# ATP prove prf x<y→x≤y #-}

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ (tipT {j} Nj) t≤i₁ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : GT j i₂ → LE-TreeItem (toTree · i₂ · tip j) i₁
  {-# ATP prove prf₁ x>y→x≰y x<y→x≤y #-}

  postulate prf₂ : LE j i₂ → LE-TreeItem (toTree · i₂ · tip j) i₁
  {-# ATP prove prf₂ x<y→x≤y #-}

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                       (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  [ prf₁ (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₁
           (&&-list₂-true₁ (≤-TreeItem-Bool Tt₁ Ni₁)
                           (≤-TreeItem-Bool Tt₂ Ni₁)
                           (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁)))

  , prf₂ (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₂
           (&&-list₂-true₂  (≤-TreeItem-Bool Tt₁ Ni₁)
                            (≤-TreeItem-Bool Tt₂ Ni₁)
                            (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁)))
  ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : LE-TreeItem (toTree · i₂ · t₁) i₁ →  -- IH.
                   GT j i₂ →
                   LE-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  {-# ATP prove prf₁ x>y→x≰y &&-list₂-true ≤-TreeItem-Bool #-}

  postulate prf₂ : LE-TreeItem (toTree · i₂ · t₂) i₁ →  --IH.
                   LE j i₂ →
                   LE-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  {-# ATP prove prf₂ &&-list₂-true ≤-TreeItem-Bool #-}

toTree-OrdTree-helper₂ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → LE i₁ i₂ →
                         Tree t →
                         LE-ItemTree i₁ t →
                         LE-ItemTree i₁ (toTree · i₂ · t)
toTree-OrdTree-helper₂ {i₁} {i₂} .{nilTree} Ni₁ Ni₂ i₁≤i₂ nilT i₁≤t = prf
  where
  postulate prf : LE-ItemTree i₁ (toTree · i₂ · nilTree)
  {-# ATP prove prf #-}

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (tipT {j} Nj) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree · i₂ · tip j)
  {-# ATP prove prf₁ x>y→x≰y #-}

  postulate prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree · i₂ · tip j)
  {-# ATP prove prf₂ #-}

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                       (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  [ prf₁ (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
           (&&-list₂-true₁ (≤-ItemTree-Bool Ni₁ Tt₁)
                           (≤-ItemTree-Bool Ni₁ Tt₂)
                           (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t)))

  , prf₂ (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
           (&&-list₂-true₂ (≤-ItemTree-Bool Ni₁ Tt₁)
                           (≤-ItemTree-Bool Ni₁ Tt₂)
                           (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t)))
  ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : LE-ItemTree i₁ (toTree · i₂ · t₁) →  -- IH.
                   GT j i₂ →
                   LE-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  {-# ATP prove prf₁ ≤-ItemTree-Bool x>y→x≰y &&-list₂-true #-}

  postulate prf₂ : LE-ItemTree i₁ (toTree · i₂ · t₂) →  --IH.
                   LE j i₂ →
                   LE-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  {-# ATP prove prf₂ ≤-ItemTree-Bool &&-list₂-true #-}
