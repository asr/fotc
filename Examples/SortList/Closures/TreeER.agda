------------------------------------------------------------------------------
-- Closures properties respect to Tree (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.TreeER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.SortList

open import LTC.Data.Nat.Type
open import LTC.Data.Nat.List.Type
open import LTC.Data.List

------------------------------------------------------------------------------
-- See the ATP version.
postulate
  toTree-Tree : {item : D}{t : D} → N item → Tree t → Tree (toTree ∙ item ∙ t)

makeTree-Tree : {is : D} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN =
  subst (λ t → Tree t) (sym (foldr-[] toTree nilTree)) nilT
makeTree-Tree (consLN {i} {is} Ni Lis) =
  subst (λ t → Tree t)
        (sym (foldr-∷ toTree nilTree i is))
        (toTree-Tree Ni (makeTree-Tree Lis))
