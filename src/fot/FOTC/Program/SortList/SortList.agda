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
open FOTC.Base.BList
open import FOTC.Data.Bool
open import FOTC.Data.List
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Tree terms.
postulate
  nil  : D
  tip  : D → D
  node : D → D → D → D

-- The tree type.
data Tree : D → Set where
  tnil  :                                         Tree nil
  ttip  : ∀ {i} → N i →                           Tree (tip i)
  tnode : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ → Tree (node t₁ i t₂)
{-# ATP axiom tnil ttip tnode #-}

------------------------------------------------------------------------------
-- Inequalites on lists and trees

-- Note from Burstall (p. 46): "The relation ≤ between lists is only an
-- ordering if nil is excluded, similarly for trees. This is untidy but
-- will not cause trouble."

postulate
  le-ItemList    : D → D → D
  le-ItemList-[] : ∀ item → le-ItemList item [] ≡ true
  le-ItemList-∷  : ∀ item i is →
                  le-ItemList item (i ∷ is) ≡ le item i && le-ItemList item is
{-# ATP axiom le-ItemList-[] le-ItemList-∷ #-}

≤-ItemList : D → D → Set
≤-ItemList item is = le-ItemList item is ≡ true
{-# ATP definition ≤-ItemList #-}

postulate
  le-Lists    : D → D → D
  le-Lists-[] : ∀ is → le-Lists [] is ≡ true
  le-Lists-∷  : ∀ i is js →
               le-Lists (i ∷ is) js ≡ le-ItemList i js && le-Lists is js
{-# ATP axiom le-Lists-[] le-Lists-∷ #-}

≤-Lists : D → D → Set
≤-Lists is js = le-Lists is js ≡ true
{-# ATP definition ≤-Lists #-}

postulate
  le-ItemTree      : D → D → D
  le-ItemTree-nil  : ∀ item → le-ItemTree item nil ≡ true
  le-ItemTree-tip  : ∀ item i → le-ItemTree item (tip i) ≡ le item i
  le-ItemTree-node : ∀ item t₁ i t₂ →
                    le-ItemTree item (node t₁ i t₂) ≡
                    le-ItemTree item t₁ && le-ItemTree item t₂
{-# ATP axiom le-ItemTree-nil le-ItemTree-tip le-ItemTree-node #-}

≤-ItemTree : D → D → Set
≤-ItemTree item t = le-ItemTree item t ≡ true
{-# ATP definition ≤-ItemTree #-}

-- This function is not defined in the paper.
postulate
  le-TreeItem      : D → D → D
  le-TreeItem-nil  : ∀ item → le-TreeItem nil item ≡ true
  le-TreeItem-tip  : ∀ i item → le-TreeItem (tip i) item ≡ le i item
  le-TreeItem-node : ∀ t₁ i t₂ item →
                    le-TreeItem (node t₁ i t₂) item ≡
                    le-TreeItem t₁ item && le-TreeItem t₂ item
{-# ATP axiom le-TreeItem-nil le-TreeItem-tip le-TreeItem-node #-}

≤-TreeItem : D → D → Set
≤-TreeItem t item = le-TreeItem t item ≡ true
{-# ATP definition ≤-TreeItem #-}

------------------------------------------------------------------------------
-- Auxiliary functions

postulate
  -- The foldr function with the last two args flipped.
  lit    : D → D → D → D
  lit-[] : ∀ f n → lit f [] n            ≡ n
  lit-∷  : ∀ f d ds n → lit f (d ∷ ds) n ≡ f · d · (lit f ds n)
{-# ATP axiom lit-[] lit-∷ #-}

------------------------------------------------------------------------------
-- Ordering functions and predicates on lists and trees

postulate
  ordList    : D → D
  ordList-[] : ordList []                ≡ true
  ordList-∷  : ∀ i is → ordList (i ∷ is) ≡ le-ItemList i is && ordList is
{-# ATP axiom ordList-[] ordList-∷ #-}

OrdList : D → Set
OrdList is = ordList is ≡ true
{-# ATP definition OrdList #-}

postulate
  ordTree      : D → D
  ordTree-nil  : ordTree nil ≡ true
  ordTree-tip  : ∀ i → ordTree (tip i) ≡ true
  ordTree-node : ∀ t₁ i t₂ →
                 ordTree (node t₁ i t₂) ≡
                 ordTree t₁ && ordTree t₂ && le-TreeItem t₁ i && le-ItemTree i t₂
{-# ATP axiom ordTree-nil ordTree-tip ordTree-node #-}

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
  toTree      : D
  toTree-nil  : ∀ item → toTree · item · nil ≡ tip item
  toTree-tip  : ∀ item i → toTree · item · (tip i) ≡
                if (le i item)
                   then (node (tip i) item (tip item))
                   else (node (tip item) i (tip i))
  toTree-node : ∀ item t₁ i t₂ →
                toTree · item · (node t₁ i t₂) ≡
                if (le i item)
                   then (node t₁ i (toTree · item · t₂))
                   else (node (toTree · item · t₁) i t₂)
{-# ATP axiom toTree-nil toTree-tip toTree-node #-}

-- The function makeTree converts a list to a tree.
makeTree : D → D
makeTree is = lit toTree is nil
{-# ATP definition makeTree #-}

-- The function flatten converts a tree to a list.
postulate
  flatten      : D → D
  flatten-nil  : flatten nil ≡ []
  flatten-tip  : ∀ i → flatten (tip i) ≡ i ∷ []
  flatten-node : ∀ t₁ i t₂ → flatten (node t₁ i t₂) ≡ flatten t₁ ++ flatten t₂
{-# ATP axiom flatten-nil flatten-tip flatten-node #-}

-- The function which sorts the list
sort : D → D
sort is = flatten (makeTree is)
{-# ATP definition sort #-}
