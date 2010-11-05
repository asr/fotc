------------------------------------------------------------------------------
-- Closures properties respect to Tree
------------------------------------------------------------------------------

module Examples.SortList.Closures.Tree where

open import LTC.Base

open import Examples.SortList.SortList
  using ( nilTree ; node ; tip
        ; makeTree
        ; toTree
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        )

-- TODO: There is a bug with the importation in agda2atp.
open import LTC.Data.Bool using ()
open import LTC.Data.List using ()

open import LTC.Data.Nat.Inequalities using ( GT ; LE )
open import LTC.Data.Nat.Inequalities.Properties using ( x>y∨x≤y ; x>y→x≰y )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type using ( N )

------------------------------------------------------------------------------

toTree-Tree : {item : D}{t : D} → N item → Tree t → Tree (toTree ∙ item ∙ t)
toTree-Tree {item} Nitem nilT = prf
  where
    postulate prf : Tree (toTree ∙ item ∙ nilTree)
    {-# ATP prove prf #-}

toTree-Tree {item} Nitem (tipT {i} Ni) = prf (x>y∨x≤y Ni Nitem)
  where
    postulate prf : GT i item ∨ LE i item → Tree (toTree ∙ item ∙ tip i)
    {-# ATP prove prf x>y→x≰y #-}
toTree-Tree {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) =
  prf (x>y∨x≤y Ni Nitem) (toTree-Tree Nitem Tt₁) ((toTree-Tree Nitem Tt₂))
  where
    postulate prf : GT i item ∨ LE i item →
                    Tree (toTree ∙ item ∙ t₁) →  -- IH.
                    Tree (toTree ∙ item ∙ t₂) →  -- IH.
                    Tree (toTree ∙ item ∙ node t₁ i t₂)
    {-# ATP prove prf x>y→x≰y #-}

makeTree-Tree : {is : D} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN = prf
  where
    postulate prf : Tree (makeTree [])
    {-# ATP prove prf #-}

makeTree-Tree (consLN {i} {is} Nn Lis) = prf (makeTree-Tree Lis)
  where
    postulate prf : Tree (makeTree is) →  -- IH.
                    Tree (makeTree (i ∷ is))
    {-# ATP prove prf toTree-Tree #-}
