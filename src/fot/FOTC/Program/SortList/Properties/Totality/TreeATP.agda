------------------------------------------------------------------------------
-- Totality properties respect to Tree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.TreeATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------

toTree-Tree : ∀ {item t} → N item → Tree t → Tree (toTree · item · t)
toTree-Tree {item} Nitem nilT = prf
  where postulate prf : Tree (toTree · item · nilTree)
        {-# ATP prove prf #-}

toTree-Tree {item} Nitem (tipT {i} Ni) = prf $ x>y∨x≤y Ni Nitem
  where postulate prf : GT i item ∨ LE i item → Tree (toTree · item · tip i)
        {-# ATP prove prf x>y→x≰y #-}
toTree-Tree {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (x>y∨x≤y Ni Nitem) (toTree-Tree Nitem Tt₁) (toTree-Tree Nitem Tt₂)
  where
  postulate prf : GT i item ∨ LE i item →
                  Tree (toTree · item · t₁) →
                  Tree (toTree · item · t₂) →
                  Tree (toTree · item · node t₁ i t₂)
  {-# ATP prove prf x>y→x≰y #-}

makeTree-Tree : ∀ {is} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN = prf
  where postulate prf : Tree (makeTree [])
        {-# ATP prove prf #-}

makeTree-Tree (consLN {i} {is} Nn Lis) = prf $ makeTree-Tree Lis
  where postulate prf : Tree (makeTree is) → Tree (makeTree (i ∷ is))
        {-# ATP prove prf toTree-Tree #-}