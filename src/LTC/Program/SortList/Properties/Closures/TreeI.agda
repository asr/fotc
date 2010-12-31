------------------------------------------------------------------------------
-- Closures properties respect to Tree
------------------------------------------------------------------------------

module LTC.Program.SortList.Properties.Closures.TreeI where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )

open import LTC.Program.SortList.SortList
  using ( lit-[] ; lit-∷
        ; makeTree
        ; nilTree
        ; toTree
        ; Tree ; nilT  -- The LTC tree type.
        )

------------------------------------------------------------------------------
-- See the ATP version.
postulate
  toTree-Tree : {item : D}{t : D} → N item → Tree t → Tree (toTree · item · t)

makeTree-Tree : {is : D} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN =
  subst (λ t → Tree t) (sym $ lit-[] toTree nilTree) nilT
makeTree-Tree (consLN {i} {is} Ni LNis) =
  subst (λ t → Tree t)
        (sym $ lit-∷ toTree i is nilTree)
        (toTree-Tree Ni (makeTree-Tree LNis))
