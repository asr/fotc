------------------------------------------------------------------------------
-- Totality properties respect to Tree
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.SortList.Properties.Totality.Tree where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.List.Type
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- See the ATP version.
postulate toTree-Tree : ∀ {item t} → N item → Tree t → Tree (toTree · item · t)

makeTree-Tree : ∀ {is} → ListN is → Tree (makeTree is)
makeTree-Tree lnnil = subst Tree (sym (lit-[] toTree nil)) tnil
makeTree-Tree (lncons {i} {is} Ni LNis) =
  subst Tree
        (sym (lit-∷ toTree i is nil))
        (toTree-Tree Ni (makeTree-Tree LNis))
