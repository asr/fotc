------------------------------------------------------------------------------
-- Totality properties respect to OrdTree
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Totality.OrdTreeATP where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Bool.PropertiesI
  using ( &&-Bool
        ; &&-proj₁
        ; &&-proj₂
        ; &&₃-proj₃
        ; &&₃-proj₄
        )
open import FOTC.Data.Nat.Inequalities using ( GT ; LE )
open import FOTC.Data.Nat.Inequalities.PropertiesATP
  using ( x<y→x≤y
        ; x>y→x≰y
        ; x>y∨x≤y
        ; x≤x
        )
open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC list of natural numbers type.
        )

open import FOTC.Program.SortList.SortList
  using ( ≤-TreeItem-node
        ; ≤-ItemTree-node
        ; LE-ItemTree
        ; LE-TreeItem
        ; makeTree
        ; nilTree ; node ; tip
        ; ordTree ; OrdTree
        ; toTree
        ; Tree ; nilT ; nodeT ; tipT  -- The FOTC tree type.
        )
open import FOTC.Program.SortList.Properties.Totality.BoolATP
  using ( ≤-ItemTree-Bool
        ; ≤-TreeItem-Bool
        ; ordTree-Bool
        )
open import FOTC.Program.SortList.Properties.Totality.TreeATP
  using ( makeTree-Tree )

------------------------------------------------------------------------------
-- Subtrees

-- If (node t₁ i t₂) is ordered then t₁ is ordered.
postulate
  leftSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                        OrdTree (node t₁ i t₂) → OrdTree t₁
-- E 1.2: CPU time limit exceeded (180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
-- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
{-# ATP prove leftSubTree-OrdTree ≤-ItemTree-Bool ≤-TreeItem-Bool &&-Bool
                                  ordTree-Bool &&-proj₁
#-}

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
postulate
  rightSubTree-OrdTree : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                         OrdTree (node t₁ i t₂) → OrdTree t₂
-- E 1.2: CPU time limit exceeded (180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove rightSubTree-OrdTree ≤-ItemTree-Bool ≤-TreeItem-Bool &&-Bool
                                   ordTree-Bool &&-proj₁
                                   &&-proj₂
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
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₁ x>y→x≰y x<y→x≤y #-}

  postulate prf₂ : LE j i₂ → LE-TreeItem (toTree · i₂ · tip j) i₁
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₂ x<y→x≤y #-}

toTree-OrdTree-helper₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                       (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  [ prf₁ (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₁
           (&&-proj₁ (≤-TreeItem-Bool Tt₁ Ni₁)
                     (≤-TreeItem-Bool Tt₂ Ni₁)
                     (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁)))

  , prf₂ (toTree-OrdTree-helper₁ Ni₁ Ni₂ i₁>i₂ Tt₂
           (&&-proj₂  (≤-TreeItem-Bool Tt₁ Ni₁)
                      (≤-TreeItem-Bool Tt₂ Ni₁)
                      (trans (sym $ ≤-TreeItem-node t₁ j t₂ i₁) t≤i₁)))
  ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : LE-TreeItem (toTree · i₂ · t₁) i₁ →  -- IH.
                   GT j i₂ →
                   LE-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₁ x>y→x≰y &&-proj₂ ≤-TreeItem-Bool #-}

  postulate prf₂ : LE-TreeItem (toTree · i₂ · t₂) i₁ →  --IH.
                   LE j i₂ →
                   LE-TreeItem (toTree · i₂ · node t₁ j t₂) i₁
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf₂ &&-proj₁ ≤-TreeItem-Bool #-}

toTree-OrdTree-helper₂ : ∀ {i₁ i₂ t} → N i₁ → N i₂ → LE i₁ i₂ →
                         Tree t →
                         LE-ItemTree i₁ t →
                         LE-ItemTree i₁ (toTree · i₂ · t)
toTree-OrdTree-helper₂ {i₁} {i₂} .{nilTree} _ _ i₁≤i₂  nilT _ = prf
  where
  postulate prf : LE-ItemTree i₁ (toTree · i₂ · nilTree)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf #-}

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (tipT {j} Nj) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree · i₂ · tip j)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₁ x>y→x≰y #-}

  postulate prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree · i₂ · tip j)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₂ #-}

toTree-OrdTree-helper₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                       (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  [ prf₁ (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
           (&&-proj₁ (≤-ItemTree-Bool Ni₁ Tt₁)
                     (≤-ItemTree-Bool Ni₁ Tt₂)
                     (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t)))

  , prf₂ (toTree-OrdTree-helper₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
           (&&-proj₂ (≤-ItemTree-Bool Ni₁ Tt₁)
                     (≤-ItemTree-Bool Ni₁ Tt₂)
                     (trans (sym $ ≤-ItemTree-node i₁ t₁ j t₂) i₁≤t)))
  ] (x>y∨x≤y Nj Ni₂)
  where
  postulate prf₁ : LE-ItemTree i₁ (toTree · i₂ · t₁) →  -- IH.
                   GT j i₂ →
                   LE-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₁ ≤-ItemTree-Bool x>y→x≰y &&-proj₂ #-}

  postulate prf₂ : LE-ItemTree i₁ (toTree · i₂ · t₂) →  --IH.
                   LE j i₂ →
                   LE-ItemTree i₁ (toTree · i₂ · node t₁ j t₂)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf₂ ≤-ItemTree-Bool &&-proj₁ #-}
