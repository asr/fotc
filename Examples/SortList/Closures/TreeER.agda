------------------------------------------------------------------------------
-- Closures properties respect to Tree (using equational reasoning)
------------------------------------------------------------------------------

module Examples.SortList.Closures.TreeER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.SortList.SortList

open import LTC.Data.Nat.Type
open import LTC.Data.Nat.List

------------------------------------------------------------------------------

-- See the ATP version.
postulate
  toTree-Tree : {item : D}{t : D} → N item → Tree t → Tree (toTree ∙ item ∙ t)

makeTree-Tree : {is : D} → List is → Tree (makeTree is)
makeTree-Tree nilL =
  subst (λ t → Tree t) (sym (foldr-[] toTree nilTree)) nilT
makeTree-Tree (consL {i} {is} Ni Lis) =
  subst (λ t → Tree t)
        (sym (foldr-∷ toTree nilTree i is))
        (toTree-Tree Ni (makeTree-Tree Lis))
