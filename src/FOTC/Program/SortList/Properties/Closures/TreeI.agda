------------------------------------------------------------------------------
-- Closures properties respect to Tree
------------------------------------------------------------------------------

module FOTC.Program.SortList.Properties.Closures.TreeI where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC natural numbers type.
        )

open import FOTC.Program.SortList.SortList
  using ( lit-[] ; lit-∷
        ; makeTree
        ; nilTree
        ; toTree
        ; Tree ; nilT  -- The FOTC tree type.
        )

------------------------------------------------------------------------------
-- See the ATP version.
postulate
  toTree-Tree : ∀ {item t} → N item → Tree t → Tree (toTree · item · t)

makeTree-Tree : ∀ {is} → ListN is → Tree (makeTree is)
makeTree-Tree nilLN =
  subst (λ t → Tree t) (sym $ lit-[] toTree nilTree) nilT
makeTree-Tree (consLN {i} {is} Ni LNis) =
  subst (λ t → Tree t)
        (sym $ lit-∷ toTree i is nilTree)
        (toTree-Tree Ni (makeTree-Tree LNis))
