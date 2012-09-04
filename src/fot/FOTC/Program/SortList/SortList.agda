------------------------------------------------------------------------------
-- Sort a list
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module define the program which sorts a list by converting it
-- into an ordered tree and then back to a list (Burstall 1969,
-- pp. 45-46).

-- References:
--
-- • R. M. Burstall. Proving properties of programs by structural
--   induction. The Computer Journal, 12(1):41–48, 1969.

module FOTC.Program.SortList.SortList where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.List
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Tree terms.
postulate
  nilTree  : D
  tip      : D → D
  node     : D → D → D → D

-- The tree type.
data Tree : D → Set where
  tnil  :                                         Tree nilTree
  ttip  : ∀ {i} → N i →                           Tree (tip i)
  tnode : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ → Tree (node t₁ i t₂)
{-# ATP axiom tnil ttip tnode #-}

------------------------------------------------------------------------------
-- Inequalites on lists and trees

-- Note from Burstall (p. 46): "The relation ≤ between lists is only an
-- ordering if nil is excluded, similarly for trees. This is untidy but
-- will not cause trouble."

postulate
  ≤-ItemList    : D → D → D
  ≤-ItemList-[] : ∀ item → ≤-ItemList item [] ≡ true
  ≤-ItemList-∷  : ∀ item i is →
                  ≤-ItemList item (i ∷ is) ≡ (item ≤ i) && ≤-ItemList item is
{-# ATP axiom ≤-ItemList-[] ≤-ItemList-∷ #-}

LE-ItemList : D → D → Set
LE-ItemList item is = ≤-ItemList item is ≡ true
{-# ATP definition LE-ItemList #-}

postulate
  ≤-Lists    : D → D → D
  ≤-Lists-[] : ∀ is → ≤-Lists [] is ≡ true
  ≤-Lists-∷  : ∀ i is js →
               ≤-Lists (i ∷ is) js ≡ ≤-ItemList i js && ≤-Lists is js
{-# ATP axiom ≤-Lists-[] ≤-Lists-∷ #-}

LE-Lists : D → D → Set
LE-Lists is js = ≤-Lists is js ≡ true
{-# ATP definition LE-Lists #-}

postulate
  ≤-ItemTree          : D → D → D
  ≤-ItemTree-nilTree  : ∀ item →   ≤-ItemTree item nilTree ≡ true
  ≤-ItemTree-tip      : ∀ item i → ≤-ItemTree item (tip i) ≡ item ≤ i
  ≤-ItemTree-node     : ∀ item t₁ i t₂ →
                          ≤-ItemTree item (node t₁ i t₂) ≡
                          ≤-ItemTree item t₁ && ≤-ItemTree item t₂
{-# ATP axiom ≤-ItemTree-nilTree ≤-ItemTree-tip ≤-ItemTree-node #-}

LE-ItemTree : D → D → Set
LE-ItemTree item t = ≤-ItemTree item t ≡ true
{-# ATP definition LE-ItemTree #-}

-- This function is not defined in the paper.
postulate
  ≤-TreeItem         : D → D → D
  ≤-TreeItem-nilTree : ∀ item →   ≤-TreeItem nilTree item ≡ true
  ≤-TreeItem-tip     : ∀ i item → ≤-TreeItem (tip i) item ≡ i ≤ item
  ≤-TreeItem-node    : ∀ t₁ i t₂ item →
                         ≤-TreeItem (node t₁ i t₂) item ≡
                         ≤-TreeItem t₁ item && ≤-TreeItem t₂ item
{-# ATP axiom ≤-TreeItem-nilTree ≤-TreeItem-tip ≤-TreeItem-node #-}

LE-TreeItem : D → D → Set
LE-TreeItem t item = ≤-TreeItem t item ≡ true
{-# ATP definition LE-TreeItem #-}

------------------------------------------------------------------------------
-- Auxiliary functions

postulate
  -- The foldr function with the last two args flipped.
  lit    : D → D → D → D
  lit-[] : ∀ f n →      lit f []       n ≡ n
  lit-∷  : ∀ f d ds n → lit f (d ∷ ds) n ≡ f · d · (lit f ds n)
{-# ATP axiom lit-[] lit-∷ #-}

------------------------------------------------------------------------------
-- Ordering functions and predicates on lists and trees

postulate
  ordList    : D → D
  ordList-[] :          ordList []       ≡ true
  ordList-∷  : ∀ i is → ordList (i ∷ is) ≡ ≤-ItemList i is && ordList is
{-# ATP axiom ordList-[] ordList-∷ #-}

OrdList : D → Set
OrdList is = ordList is ≡ true
{-# ATP definition OrdList #-}

postulate
  ordTree         : D → D
  ordTree-nilTree :       ordTree nilTree ≡ true
  ordTree-tip     : ∀ i → ordTree (tip i) ≡ true
  ordTree-node    : ∀ t₁ i t₂ →
                      ordTree (node t₁ i t₂) ≡
                      ordTree t₁ && ordTree t₂ && ≤-TreeItem t₁ i && ≤-ItemTree i t₂
{-# ATP axiom ordTree-nilTree ordTree-tip ordTree-node #-}

OrdTree : D → Set
OrdTree t = ordTree t ≡ true
{-# ATP definition OrdTree #-}

------------------------------------------------------------------------------
-- The program

-- The function toTree adds an item to a tree.

-- The items have an ordering ≤ defined over them. The item held at a
-- node of the tree is chosen so that the left subtree has items not
-- greater than it and the right subtree has items not less than it.

postulate
  toTree          : D
  toTree-nilTree  : ∀ item →   toTree · item · nilTree ≡ tip item
  toTree-tip      : ∀ item i → toTree · item · (tip i) ≡
                    if (i ≤ item)
                      then (node (tip i) item (tip item))
                      else (node (tip item) i (tip i))
  toTree-node     : ∀ item t₁ i t₂ →
                    toTree · item · (node t₁ i t₂) ≡
                       if (i ≤ item)
                         then (node t₁ i (toTree · item · t₂))
                         else (node (toTree · item · t₁) i t₂)
{-# ATP axiom toTree-nilTree toTree-tip toTree-node #-}

-- The function makeTree converts a list to a tree.
makeTree : D → D
makeTree is = lit toTree is nilTree
{-# ATP definition makeTree #-}

-- The function flatten converts a tree to a list.
postulate
  flatten         : D → D
  flatten-nilTree :       flatten nilTree ≡ []
  flatten-tip     : ∀ i → flatten (tip i) ≡ i ∷ []
  flatten-node    : ∀ t₁ i t₂ →
                    flatten (node t₁ i t₂)  ≡ flatten t₁ ++ flatten t₂
{-# ATP axiom flatten-nilTree flatten-tip flatten-node #-}

-- The function which sorts the list
sort : D → D
sort is = flatten (makeTree is)
{-# ATP definition sort #-}
