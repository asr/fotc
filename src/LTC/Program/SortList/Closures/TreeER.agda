------------------------------------------------------------------------------
-- Closures properties respect to Tree (using equational reasoning)
------------------------------------------------------------------------------

-- TODO: This module is called TreeER, but it not used ER.

module LTC.Program.SortList.Closures.TreeER where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )
open import LTC.Data.List using ( foldr-[] ; foldr-∷ )

open import LTC.Program.SortList.SortList
  using ( makeTree
        ; nilTree
        ; toTree
        ; Tree ; nilT  -- The LTC tree type.
        )

------------------------------------------------------------------------------
-- See the ATP version.
postulate
  toTree-Tree : {item : D}{t : D} → N item → Tree t → Tree (toTree ∙ item ∙ t)

makeTree-Tree : {is : D} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN =
  subst (λ t → Tree t) (sym $ foldr-[] toTree nilTree) nilT
makeTree-Tree (consLN {i} {is} Ni Lis) =
  subst (λ t → Tree t)
        (sym $ foldr-∷ toTree nilTree i is)
        (toTree-Tree Ni (makeTree-Tree Lis))
