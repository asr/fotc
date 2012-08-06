------------------------------------------------------------------------------
-- Totality properties respect to Tree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.SortList.Properties.Totality.TreeI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList

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
