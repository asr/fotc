------------------------------------------------------------------------------
-- Totality properties respect to Tree
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Totality.TreeATP where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat.Inequalities.PropertiesATP using ( x>y∨x≤y ; x>y→x≰y )
open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC natural numbers type.
        )

open import FOTC.Program.SortList.SortList
  using ( nilTree ; node ; tip
        ; makeTree
        ; toTree
        ; Tree ; nilT ; nodeT ; tipT  -- The FOTC tree type.
        )

open import FOTC.Data.Nat.Inequalities using ( GT ; LE )

------------------------------------------------------------------------------

toTree-Tree : ∀ {item t} → N item → Tree t → Tree (toTree · item · t)
toTree-Tree {item} Nitem nilT = prf
  where
  postulate prf : Tree (toTree · item · nilTree)
  {-# ATP prove prf #-}

toTree-Tree {item} Nitem (tipT {i} Ni) = prf $ x>y∨x≤y Ni Nitem
  where
  postulate prf : GT i item ∨ LE i item → Tree (toTree · item · tip i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf x>y→x≰y #-}
toTree-Tree {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (x>y∨x≤y Ni Nitem) (toTree-Tree Nitem Tt₁) (toTree-Tree Nitem Tt₂)
  where
  postulate prf : GT i item ∨ LE i item →
                  Tree (toTree · item · t₁) →  -- IH.
                  Tree (toTree · item · t₂) →  -- IH.
                  Tree (toTree · item · node t₁ i t₂)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf x>y→x≰y #-}

makeTree-Tree : ∀ {is} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN = prf
  where
  postulate prf : Tree (makeTree [])
  {-# ATP prove prf #-}

makeTree-Tree (consLN {i} {is} Nn Lis) = prf $ makeTree-Tree Lis
  where
  postulate prf : Tree (makeTree is) →  -- IH.
                  Tree (makeTree (i ∷ is))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf toTree-Tree #-}
